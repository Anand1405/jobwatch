#!/usr/bin/env python3
"""job-search engine: poll job APIs -> score vs profile -> push NEW matches to Telegram.

Stdlib only. Commands:
  init                      create ~/.job-search with config/profile/companies templates
  tg-chat-id                print chat ids seen by the bot (message your bot first)
  tg-test                   send a test Telegram message
  run [--dry-run] [--sources a,b] [--max-age-min N]   one polling cycle
  daemon                    poll forever (singleton)
  ingest FILE|-             score+alert jobs from JSON list (agent-reach / browser sweeps)
  status                    counts + last run per source
  show ID                   print stored job description for an alerted job
"""
import argparse, datetime as dt, hashlib, html, json, logging, os, random, re, socket
import sqlite3, sys, threading, time, urllib.error, urllib.request
from concurrent.futures import ThreadPoolExecutor
from email.utils import parsedate_to_datetime
from logging.handlers import RotatingFileHandler
from pathlib import Path
import xml.etree.ElementTree as ET

SKILL_DIR = Path(__file__).resolve().parent.parent
HOME = Path(os.environ.get("JOBSEARCH_HOME") or Path.home() / ".job-search")
UA = "Mozilla/5.0 (compatible; job-search/1.0)"
LOCK_PORT = 47831

FX = {"USD": 1.0, "EUR": 1.08, "GBP": 1.27, "CAD": 0.73, "AUD": 0.65, "SGD": 0.74, "CHF": 1.12}
PER_MULT = {"year": 1, "month": 12, "week": 52, "day": 260, "hour": 2080}
SOURCE_MAX_AGE_H = {"remotive": 72}  # remotive delays listings ~24h
DEFAULT_INTERVALS = {"remotive": 360, "hn_hiring": 20, "hn_jobs": 15, "remoterocketship": 15, "ats": 10}

log = logging.getLogger("jobsearch")

# ----------------------------------------------------------------- utils
def setup_logging():
    HOME.mkdir(parents=True, exist_ok=True)
    log.setLevel(logging.INFO)
    if not log.handlers:
        fh = RotatingFileHandler(HOME / "jobsearch.log", maxBytes=1_000_000, backupCount=3, encoding="utf-8")
        fh.setFormatter(logging.Formatter("%(asctime)s %(levelname)s %(message)s"))
        sh = logging.StreamHandler(sys.stdout)
        sh.setFormatter(logging.Formatter("%(message)s"))
        log.addHandler(fh); log.addHandler(sh)


def http(url, headers=None, data=None, timeout=25, raw=False):
    h = {"User-Agent": UA, "Accept": "application/json,text/html,*/*"}
    h.update(headers or {})
    req = urllib.request.Request(url, headers=h, data=data)
    last = None
    for attempt in (1, 2):
        try:
            with urllib.request.urlopen(req, timeout=timeout) as r:
                body = r.read()
            return body if raw else json.loads(body.decode("utf-8", "replace"))
        except urllib.error.HTTPError as e:
            if e.code in (400, 401, 403, 404, 410):
                raise
            last = e
        except Exception as e:  # network blips
            last = e
        time.sleep(1.5)
    raise last


TAG = re.compile(r"<[^>]+>")
def clean(s):
    s = html.unescape(s or "")
    s = re.sub(r"<(br|/p|/li|/div|/h\d|/tr)[^>]*>", "\n", s, flags=re.I)
    s = html.unescape(TAG.sub(" ", s))
    s = re.sub(r"[ \t\r\f\v ]+", " ", s)
    return re.sub(r"\n\s*\n+", "\n", s).strip()


def iso_epoch(s):
    if not s:
        return None
    try:
        d = dt.datetime.fromisoformat(str(s).strip().replace("Z", "+00:00"))
    except ValueError:
        return None
    if d.tzinfo is None:
        d = d.replace(tzinfo=dt.timezone.utc)
    return d.timestamp()


def to_epoch(v):
    if v in (None, "", 0):
        return None
    if isinstance(v, (int, float)) or str(v).isdigit():
        v = float(v)
        return v / 1000 if v > 1e11 else v
    return iso_epoch(v)


def J(source, jid, title, company, url, posted, location="", remote=None, employment="", text="", sal=None, sal_text=""):
    return dict(source=source, id=f"{source}:{jid}", title=(title or "").strip(), company=(company or "").strip(),
                url=url, posted=posted, location=(location or "").strip(), remote=remote,
                employment=(employment or "").lower(), text=(text or "")[:8000], sal=sal, sal_text=sal_text or "")


def slugify(s):
    return re.sub(r"[^a-z0-9]+", "-", s.lower()).strip("-")


def tokens(s):
    return re.findall(r"[a-z0-9+#.]+", s.lower())


IST = dt.timezone(dt.timedelta(hours=5, minutes=30))


def when_str(posted):
    """'12 min ago (07 Nov 10:42 IST)'"""
    if not posted:
        return "time unknown"
    return f"{age_str(posted)} ({dt.datetime.fromtimestamp(posted, IST).strftime('%d %b %H:%M')} IST)"


def age_str(posted):
    if not posted:
        return "time unknown"
    m = max(0, int((time.time() - posted) / 60))
    return f"{m} min ago" if m < 90 else (f"{m // 60} h ago" if m < 2880 else f"{m // 1440} d ago")

# ----------------------------------------------------------------- salary
MONEY = re.compile(r"(?P<cur>US\$|USD|EUR|GBP|CAD|AUD|SGD|[$€£])\s?(?P<n>\d[\d,]*(?:\.\d+)?)\s?(?P<k>[kK])?(?![\w])", re.I)
MONEY2 = re.compile(r"(?P<n>\d[\d,]*(?:\.\d+)?)\s?(?P<k>[kK])?\s?(?P<cur>USD|EUR|GBP)\b", re.I)
RANGE = re.compile(r"\s*(?:-|–|—|to|and)\s*(?:US\$|USD|EUR|GBP|[$€£])?\s?(?P<n>\d[\d,]*(?:\.\d+)?)\s?(?P<k>[kK])?", re.I)
CURMAP = {"$": "USD", "us$": "USD", "usd": "USD", "€": "EUR", "eur": "EUR", "£": "GBP", "gbp": "GBP",
          "cad": "CAD", "aud": "AUD", "sgd": "SGD"}
PER_PATS = [("hour", r"/\s?(?:hr|hour|h)\b|per hour|an hour|hourly|/hour"), ("month", r"/\s?(?:mo|month)\b|per month|monthly"),
            ("week", r"/\s?(?:wk|week)\b|per week|weekly"), ("day", r"/\s?day\b|per day|daily|day rate"),
            ("year", r"/\s?(?:yr|year)\b|per year|annual|a year|p\.a\.|per annum")]


def _val(n, k):
    v = float(n.replace(",", ""))
    return v * 1000 if k else v


def parse_salary(text):
    """First plausible salary in free text -> {min,max,cur,per} or None."""
    if not text:
        return None
    toks = []
    for m in MONEY.finditer(text):
        toks.append((m.start(), m.end(), m.group("cur"), m.group("n"), m.group("k"), None))
    for m in MONEY2.finditer(text):
        st = m.start()
        pre = re.search(r"(\d[\d,]*(?:\.\d+)?)\s?([kK])?\s?(?:-|–|—|to)\s*$", text[max(0, st - 20):st])
        if pre:  # "40-60 USD/hr": range's low end sits before the matched number
            toks.append((max(0, st - 20) + pre.start(), m.end(), m.group("cur"), pre.group(1), pre.group(2),
                         _val(m.group("n"), m.group("k") or pre.group(2))))
        else:
            toks.append((st, m.end(), m.group("cur"), m.group("n"), m.group("k"), None))
    for start, end, cur, n, k, pre_hi in sorted(toks, key=lambda t: t[0]):
        lo = _val(n, k)
        hi = pre_hi if pre_hi is not None else lo
        rm = None if pre_hi is not None else RANGE.match(text, end)
        if hi < lo:
            lo, hi = hi, lo
        if rm:
            hk = rm.group("k") or (k if k and _val(rm.group("n"), None) < 1000 else None)
            hi = _val(rm.group("n"), hk)
            end = rm.end()
            if hi < lo:
                lo, hi = hi, lo
        win = (text[max(0, start - 30):start] + " " + text[end:end + 30]).lower()
        per = next((p for p, pat in PER_PATS if re.search(pat, win)), None)
        if per is None:
            per = "year" if lo >= 1000 else None
        if per is None:
            continue
        mult = PER_MULT[per]
        ann = hi * mult
        if per == "hour" and not (8 <= hi <= 600):
            continue
        if per != "hour" and not (15_000 <= ann <= 1_500_000):
            continue
        return dict(min=lo, max=hi, cur=CURMAP.get(cur.lower(), "USD"), per=per)
    return None


def sal_annual(sal):
    fx = FX.get(sal["cur"])
    if fx is None:
        return None, None
    m = PER_MULT[sal["per"]]
    return sal["min"] * fx * m, sal["max"] * fx * m


def fmt_sal(sal):
    if not sal:
        return "unlisted"
    sym = {"USD": "$", "EUR": "€", "GBP": "£"}.get(sal["cur"], sal["cur"] + " ")
    def f(v):
        return f"{v / 1000:.0f}k" if v >= 10000 else f"{v:g}"
    rng = f(sal["min"]) if sal["min"] == sal["max"] else f"{f(sal['min'])}–{sym}{f(sal['max'])}"
    return f"{sym}{rng} /{sal['per'][:2] if sal['per'] != 'month' else 'mo'}".replace("/ye", "/yr").replace("/ho", "/hr")

# ----------------------------------------------------------------- geo / contract
GEO_POS = ["worldwide", "anywhere", "global", "india", "apac", "asia", "any location", "international",
           "world wide", "all countries", "remote - any", "south asia", "gmt+5", "utc+5", "earth", "everywhere"]
GEO_NEG_TEXT = [
    r"\b(?:us|u\.s\.|usa|united states)[\s-]*(?:only|based only|residents? only|citizens? only)\b",
    r"\bmust (?:be (?:located|based)|reside|live|work) (?:in|from) (?:the )?(?:us|u\.s\.|usa|united states|uk|europe|eu|canada|latam|germany|brazil)\b",
    r"\b(?:authori[sz]ed|eligible|legally authori[sz]ed) to work in (?:the )?(?:us|u\.s\.|united states|uk|eu|canada)\b",
    r"\bwork authori[sz]ation (?:in|for) (?:the )?(?:us|united states|uk|canada)\b",
    r"\bsecurity clearance\b", r"\bus citizens?\b", r"\b(?:eu|european) (?:citizens?|residents?) only\b",
    r"\bno (?:sponsorship|visa)\b.{0,40}\b(?:us|united states)\b", r"\bresidents? of (?:the )?(?:us|united states|uk|canada)\b",
    r"\bremote\s*\((?:us|usa|u\.s\.|canada|uk|eu|europe)(?: only)?\)",
]
EMPTY_LOC = {"", "remote", "remote only", "fully remote", "100% remote", "n/a", "remote - remote", "distributed", "remote (flexible)"}


def geo_check(location, text, remote_flag):
    """-> (ok, label, flags)"""
    flags = []
    t = (text or "")[:6000].lower()
    for pat in GEO_NEG_TEXT:
        m = re.search(pat, t)
        if m:
            return False, "geo-restricted: " + m.group(0)[:40], flags
    loc = (location or "").lower().strip()
    if re.search(r"overlap|pst|est\b|cst\b|pacific|eastern time|us time ?zones?|working hours", t[:3000]):
        flags.append("timezone overlap may be required")
    if loc in EMPTY_LOC:
        flags.append("location unclear - verify India eligibility")
        return True, "remote (location unspecified)", flags
    for g in GEO_POS:
        if g in loc:
            # "Worldwide except US" style
            if re.search(r"(?:except|excluding|not)\s+(?:the )?(?:india)", loc):
                return False, "excludes India", flags
            return True, "worldwide/India-eligible", flags
    return False, f"location: {location[:40]}", flags


CONTRACT_WORDS = re.compile(r"\b(contract|contractor|freelance|temporary|temp|fixed[- ]term|b2b)\b", re.I)
DUR = re.compile(r"(\d{1,2})\s*(?:\+|-|to|–)?\s*(\d{1,2})?\s*[- ]?(months?|mos?\b|years?|yrs?\b)", re.I)


def contract_info(job):
    """-> (is_contract, months or None)"""
    emp = job["employment"]
    head = (job["title"] + " " + emp + " " + job["text"][:600])
    is_c = bool(CONTRACT_WORDS.search(job["title"] + " " + emp)) or bool(
        re.search(r"\b(independent contractor|contract role|contract position|\d+[- ]month contract|contract to hire)\b", head, re.I))
    if not is_c:
        return False, None
    t = job["text"]
    best = None
    for m in DUR.finditer(t):
        ctx = t[max(0, m.start() - 70):m.end() + 40].lower()
        if not re.search(r"contract|duration|engagement|term|initial|assignment|project|length|period", ctx):
            continue
        n = int(m.group(2) or m.group(1))
        unit = m.group(3).lower()
        months = n * 12 if unit.startswith(("y",)) else n
        best = max(best or 0, months)
    if best is None and re.search(r"long[- ]term|ongoing|indefinite|permanent contract|renewable|12\+|1\+ year", t, re.I):
        best = 12
    return True, best

# ----------------------------------------------------------------- scoring
SPONSOR_POS = re.compile(r"visa sponsor|sponsor(?:s|ship)?(?: a| your)?(?: work)? visa|we (?:will |can )?sponsor|sponsorship (?:is )?(?:available|provided|offered)|"
                         r"relocation (?:assistance|package|support|bonus|allowance|budget)|relocat\w+ (?:to|support|assistance)|blue card|skilled worker visa|"
                         r"h-?1b (?:sponsor|transfer)|work permit (?:support|sponsor|provided)|global talent|tech\.?pass|employment pass|visa support|immigration support", re.I)
SPONSOR_NEG = re.compile(r"no (?:visa )?sponsorship|(?:unable|not able|cannot|can't|won't|will not|do not|don't|does not) (?:to )?(?:offer |provide )?(?:visa )?sponsor|"
                         r"without (?:visa )?sponsorship|sponsorship (?:is )?not (?:available|offered|provided)|must (?:already )?(?:have|hold) (?:the )?(?:right|work authori)|"
                         r"no relocation", re.I)
REMOTE_REJECTS = ("geo-restricted", "location:", "not remote", "remote not stated", "excludes India")


def evaluate(job, P, C):
    """Remote/India path first; if that fails on geo/remote grounds, try relocation+visa-sponsorship path."""
    ev = _evaluate(job, P, C, "remote")
    rl = P.get("relocation") or {}
    if not ev["ok"] and rl.get("enabled") and ev["reject"].startswith(REMOTE_REJECTS):
        ev2 = _evaluate(job, P, C, "reloc")
        if ev2["ok"]:
            return ev2
    return ev


YEARS_RE = re.compile(r"(\d{1,2})\s*(?:\+|plus)?\s*(?:-|–|to)?\s*(\d{1,2})?\s*\+?\s*(?:years?|yrs?)\b", re.I)


def required_years(text):
    """Highest 'N+ years ... experience' lower bound mentioned in the JD, or None."""
    best = None
    t = text or ""
    for m in YEARS_RE.finditer(t):
        n = int(m.group(1))
        if not 1 <= n <= 20:
            continue
        ctx = t[max(0, m.start() - 60):m.end() + 70].lower()
        if not re.search(r"experience|exp\b|background|track record|working with|hands-on", ctx):
            continue
        if re.search(r"founded|in business|history of|over the (?:past|last) \d|years? (?:ago|old)|warranty|trial|guarantee", ctx):
            continue
        best = max(best or 0, n)
    return best


SENIOR_TITLE = re.compile(r"\b(senior|sr\.?|lead|principal|staff|head)\b", re.I)


def _evaluate(job, P, C, mode="remote"):
    """-> dict(ok, score, reasons, flags, tier, reject)"""
    RL = P.get("relocation") or {}
    def rej(why):
        return dict(ok=False, score=0, reasons=[], flags=[], tier="", reject=why)

    title_l = job["title"].lower()
    blob = f"{job['title']}\n{job['location']}\n{job['text']}".lower()
    for w in P.get("exclude_title_words", []):
        if re.search(r"(?<![\w])" + re.escape(w.lower()) + r"(?![\w])", title_l):
            return rej(f"title excluded: {w}")
    if re.search(r"\b(intern|internship|part[- ]time|apprentice)\b", title_l + " " + job["employment"]):
        return rej("not full-time/contract")
    flags, geo_label = [], ""
    if mode == "remote":
        if job.get("remote") is False:
            return rej("not remote")
        if job.get("remote") is None and "remote" not in blob:
            return rej("remote not stated")
        ok, geo_label, flags = geo_check(job["location"], job["text"], job.get("remote"))
        if not ok:
            return rej(geo_label)
    else:
        txt = job["text"][:8000]
        if SPONSOR_NEG.search(txt):
            return rej("no sponsorship")
        if not (job.get("sponsor") or SPONSOR_POS.search(txt)):
            return rej("no visa/relocation signal")
        cs = [c.lower() for c in RL.get("countries", [])]
        loc_l = (job["location"] + " " + txt[:300]).lower()
        if cs and not any(c in loc_l for c in cs):
            return rej("country not in relocation list")
        geo_label = "relocation+visa"

    # title / skills
    best, hit = 0, None
    for t in P.get("target_titles", []):
        tl = t.lower()
        if re.search(r"(?<![\w])" + re.escape(tl) + r"(?![\w])", title_l):
            best, hit = 40, t
            break
        tkl, ttl = tokens(t), tokens(job["title"])
        if not tkl:
            continue
        # ordered match with <=2 filler words between target words ("Senior Software Engineer, AI" ~ "Software Engineer AI")
        pos, ok_seq, last = 0, True, -1
        for w in tkl:
            try:
                i = ttl.index(w, pos)
            except ValueError:
                ok_seq = False
                break
            if last >= 0 and i - last > 3:
                ok_seq = False
                break
            last, pos = i, i + 1
        frac = len(set(tkl) & set(ttl)) / len(set(tkl))
        sc = 34 if ok_seq else (22 if frac >= 0.66 and len(tkl) >= 3 and not ok_seq and False else 0)
        if sc > best:
            best, hit = sc, t
    if best == 0:
        return rej("title not a target")
    skills = [s for s in P.get("skills", []) if re.search(r"(?<![\w+#])" + re.escape(s.lower()) + r"(?![\w+#])", blob)]
    anyreq = P.get("must_have_any", [])
    if anyreq and not any(re.search(r"(?<![\w+#])" + re.escape(s.lower()) + r"(?![\w+#])", blob) for s in anyreq):
        return rej("none of must_have_any skills")
    score = best + min(30, len(skills) * 5)
    reasons = [f"title~{hit}"] + ([f"skills: {', '.join(skills[:6])}"] if skills else [])
    # experience fit (profile.years_experience, default 4)
    mine = P.get("years_experience", 4)
    need = required_years(job["text"])
    job["_need"], job["_mine"], job["_mode"] = need, mine, mode
    cap_y = P.get("max_required_years", mine + 1)
    if need is not None:
        if need > cap_y:
            return rej(f"needs {need}+ yrs (you ~{mine})")
        if need == cap_y and need > mine:
            score -= 15
            flags.append(f"asks {need}+ yrs (you ~{mine}) - stretch")
        elif need <= mine:
            score += 8
            reasons.append(f"exp ok ({need}+ yrs)")
        else:
            score -= 5
    elif SENIOR_TITLE.search(job["title"]):
        score -= 8
        flags.append("senior title, years not stated")
    if mode == "reloc":
        score += 10
        reasons.append("visa/relocation support")
    if "worldwide" in geo_label:
        score += 5
        reasons.append("worldwide/India-ok")

    # contract
    is_c, months = contract_info(job)
    min_m = P.get("min_contract_months", 12)
    if mode == "reloc":
        if is_c:
            flags.append("contract role - sponsorship less likely")
    elif is_c:
        if months is not None and months < min_m:
            return rej(f"contract {months}mo < {min_m}mo")
        if months is None:
            flags.append("CONTRACT length unknown - confirm >=12 months")
        else:
            score += 3
            reasons.append(f"contract ~{months}mo")

    # salary
    sal = job.get("sal") or parse_salary(job["sal_text"]) or parse_salary(job["text"][:5000])
    tier = ""
    if sal:
        if sal["cur"] == "INR":
            return rej("INR pay")
        lo_a, hi_a = sal_annual(sal)
        if hi_a is None:
            flags.append(f"salary in {sal['cur']} - check")
            sal = None
    if sal:
        _, hi_a = sal_annual(sal)
        min_ann = RL.get("min_annual_usd", 110000) if mode == "reloc" else P.get("min_annual_usd", 150000)
        hourly_ok = mode == "remote" and is_c and (hi_a / 2080) >= P.get("min_hourly_usd", 50)
        annual_ok = hi_a >= min_ann
        if not (hourly_ok or annual_ok):
            return rej(f"pay {fmt_sal(sal)} below target")
        score += 25 if (sal["min"] * FX.get(sal["cur"], 1) * PER_MULT[sal["per"]] >= min_ann or hourly_ok) else 15
        reasons.append("pay meets target")
        tier = "🔥" if score >= 75 else "✅"
        if mode == "reloc":
            tier = "✈️"
    else:
        if not (RL.get("allow_unknown_salary", False) if mode == "reloc" else P.get("allow_unknown_salary", True)):
            return rej("salary unlisted")
        flags.append("salary unlisted")
        tier = "✈️❔" if mode == "reloc" else "❔"
    job["_sal"] = sal

    # recency
    if job.get("posted"):
        mins = (time.time() - job["posted"]) / 60
        score += 10 if mins <= 30 else (5 if mins <= 120 else 0)
    min_score = C.get("min_score", 50)
    if not sal:
        min_score = max(min_score, C.get("unknown_salary_min_score", 60))
    if score < min_score:
        return rej(f"score {score} < {min_score}")
    return dict(ok=True, score=min(score, 100), reasons=reasons, flags=flags, tier=tier, reject="")

# ----------------------------------------------------------------- fetchers
class Ctx:
    def __init__(self, P, C, seen):
        self.P, self.C, self.seen = P, C, seen


def f_remoteok(ctx):
    out = []
    for r in http("https://remoteok.com/api")[1:]:
        sal = None
        if r.get("salary_min") and r.get("salary_max"):
            sal = dict(min=float(r["salary_min"]), max=float(r["salary_max"]), cur="USD", per="year")
        out.append(J("remoteok", r["id"], r.get("position"), r.get("company"), r.get("url") or r.get("apply_url"),
                     to_epoch(r.get("epoch")) or iso_epoch(r.get("date")), r.get("location") or "Worldwide", True, "",
                     clean(r.get("description")) + " " + " ".join(r.get("tags") or []), sal))
    return out


def f_remotive(ctx):
    out = []
    for r in http("https://remotive.com/api/remote-jobs?limit=150").get("jobs", []):
        out.append(J("remotive", r["id"], r["title"], r["company_name"], r["url"], iso_epoch(r.get("publication_date")),
                     r.get("candidate_required_location"), True, r.get("job_type", ""), clean(r.get("description")),
                     None, r.get("salary") or ""))
    return out


def f_jobicy(ctx):
    out = []
    for r in http("https://jobicy.com/api/v2/remote-jobs?count=50").get("jobs", []):
        sal = None
        lo, hi = r.get("annualSalaryMin") or r.get("salaryMin"), r.get("annualSalaryMax") or r.get("salaryMax")
        if lo and hi:
            sal = dict(min=float(lo), max=float(hi), cur=(r.get("salaryCurrency") or "USD").upper(),
                       per={"hourly": "hour", "monthly": "month"}.get((r.get("salaryPeriod") or "").lower(), "year"))
        jt = r.get("jobType")
        out.append(J("jobicy", r["id"], r.get("jobTitle"), r.get("companyName"), r.get("url"), iso_epoch(r.get("pubDate")),
                     r.get("jobGeo") if isinstance(r.get("jobGeo"), str) else ", ".join(r.get("jobGeo") or []), True,
                     ", ".join(jt) if isinstance(jt, list) else (jt or ""), clean(r.get("jobDescription") or r.get("jobExcerpt")), sal))
    return out


def f_himalayas(ctx):
    out = []
    for off in range(0, 100, 20):
        try:
            data = http(f"https://himalayas.app/jobs/api?limit=20&offset={off}")
        except Exception:
            break
        for r in data.get("jobs", []):
            sal = None
            if r.get("minSalary") and r.get("maxSalary"):
                per = {"hourly": "hour", "monthly": "month", "weekly": "week"}.get((r.get("salaryPeriod") or "").lower(), "year")
                sal = dict(min=float(r["minSalary"]), max=float(r["maxSalary"]), cur=(r.get("currency") or "USD").upper(), per=per)
            locs = r.get("locationRestrictions") or []
            loc = "Worldwide" if not locs else ", ".join(map(str, locs))
            out.append(J("himalayas", r.get("guid") or r.get("applicationLink"), r.get("title"), r.get("companyName"),
                         r.get("applicationLink") or r.get("guid"), to_epoch(r.get("pubDate")), loc, True,
                         r.get("employmentType", ""), clean(r.get("description") or r.get("excerpt")), sal))
        if len(data.get("jobs", [])) < 20:
            break
    return out


def f_workingnomads(ctx):
    out = []
    for r in http("https://www.workingnomads.com/api/exposed_jobs/"):
        out.append(J("workingnomads", slugify(r["url"]), r["title"], r.get("company_name"), r["url"], iso_epoch(r.get("pub_date")),
                     r.get("location") or "Anywhere", True, "", clean(r.get("description")) + " " + (r.get("tags") or "")))
    return out


WWR_FEEDS = ["remote-jobs", "categories/remote-programming-jobs", "categories/remote-back-end-programming-jobs",
             "categories/remote-full-stack-programming-jobs", "categories/remote-devops-sysadmin-jobs",
             "categories/remote-product-jobs", "categories/remote-front-end-programming-jobs"]


def f_wwr(ctx):
    out = []
    for feed in WWR_FEEDS:
        try:
            root = ET.fromstring(http(f"https://weworkremotely.com/{feed}.rss", raw=True))
        except Exception as e:
            log.warning("wwr %s: %s", feed, e)
            continue
        for it in root.iter("item"):
            g = lambda k: (it.findtext(k) or "")
            title = g("title")
            comp, _, ttl = title.partition(": ")
            try:
                posted = parsedate_to_datetime(g("pubDate")).timestamp()
            except Exception:
                posted = None
            out.append(J("wwr", g("guid") or g("link"), ttl or title, comp if ttl else "", g("link"), posted,
                         g("region") or "Anywhere in the World", True, g("type"), clean(g("description"))))
    return out


def f_arbeitnow(ctx):
    """Germany/EU roles flagged by Arbeitnow as visa-sponsoring (relocation path)."""
    out = []
    for r in http("https://www.arbeitnow.com/api/job-board-api?visa_sponsorship=true").get("data", []):
        loc = r.get("location") or ""
        j = J("arbeitnow", r["slug"], r.get("title"), r.get("company_name"), r.get("url"), to_epoch(r.get("created_at")),
              loc or "Germany", bool(r.get("remote")), ", ".join(r.get("job_types") or []),
              clean(r.get("description")) + " " + " ".join(r.get("tags") or []))
        j["sponsor"] = True
        out.append(j)
    return out


def f_hn_jobs(ctx):
    out = []
    for r in http("https://hn.algolia.com/api/v1/search_by_date?tags=job&hitsPerPage=60").get("hits", []):
        title = r.get("title") or ""
        comp = re.split(r"\s+(?:\(YC|is hiring|is looking|hiring)", title)[0]
        out.append(J("hn_jobs", r["objectID"], title, comp, r.get("url") or f"https://news.ycombinator.com/item?id={r['objectID']}",
                     r.get("created_at_i"), "", None, "", clean(r.get("story_text") or "") + " " + title))
    return out


def f_hn_hiring(ctx):
    out = []
    hits = http("https://hn.algolia.com/api/v1/search_by_date?tags=story,author_whoishiring&hitsPerPage=6").get("hits", [])
    story = next((h for h in hits if "who is hiring" in (h.get("title") or "").lower()), None)
    if not story:
        return out
    url = f"https://hn.algolia.com/api/v1/search_by_date?tags=comment,story_{story['objectID']}&hitsPerPage=120"
    for r in http(url).get("hits", []):
        if r.get("parent_id") != int(story["objectID"]):
            continue
        txt = clean(r.get("comment_text"))
        first = txt.split("\n")[0]
        if "remote" not in txt[:600].lower():
            continue
        parts = [p.strip() for p in first.split("|")]
        comp = parts[0][:60] if parts else ""
        role = next((p for p in parts[1:] if re.search(r"engineer|developer|architect|scientist|lead|manager|designer|devops|sre", p, re.I)),
                    parts[1] if len(parts) > 1 else first[:80])
        loc = next((p for p in parts if re.search(r"remote|worldwide|anywhere|global", p, re.I)), "")
        out.append(J("hn_hiring", r["objectID"], role, comp, f"https://news.ycombinator.com/item?id={r['objectID']}",
                     r.get("created_at_i"), loc, True, "", txt))
    return out


def f_remoterocketship(ctx):
    P = ctx.P
    slugs = P.get("remoterocketship_slugs") or sorted({slugify(t) for t in P.get("target_titles", [])})
    out = []
    for slug in slugs:
        try:
            h = http(f"https://www.remoterocketship.com/jobs/{slug}", raw=True).decode("utf-8", "replace")
        except urllib.error.HTTPError:
            continue
        m = re.search(r'<script id="__NEXT_DATA__"[^>]*>(.*?)</script>', h, re.S)
        if not m:
            continue
        for r in json.loads(m.group(1)).get("props", {}).get("pageProps", {}).get("initialJobOpenings", []) or []:
            sr = r.get("salaryRange") or {}
            sal = None
            if sr.get("min") and sr.get("max"):
                st = (sr.get("salaryType") or "").lower()
                sal = dict(min=float(sr["min"]), max=float(sr["max"]), cur=(sr.get("currencyCode") or "USD").upper(),
                           per="hour" if "hour" in st else ("month" if "month" in st else "year"))
            loc = r.get("location") or ""
            if r.get("locationCountries"):
                loc += " " + ", ".join(map(str, r["locationCountries"]))
            out.append(J("remoterocketship", r["id"], r.get("roleTitle"), (r.get("company") or {}).get("name"), r.get("url"),
                         iso_epoch(r.get("created_at")), loc, (r.get("locationType") or "").lower() == "remote" or None,
                         r.get("employmentType", ""), (r.get("jobDescriptionSummary") or "") + " " + " ".join(r.get("techStack") or []), sal))
        time.sleep(0.4)
    return out

# --- ATS (Greenhouse / Lever / Ashby) company boards: fastest source, no key needed
def _title_geo_prefilter(ctx, title, loc):
    if not any(set(tokens(t)) <= set(tokens(title)) for t in ctx.P.get("target_titles", [])):
        return False
    if any(re.search(r"(?<![\w])" + re.escape(w.lower()) + r"(?![\w])", title.lower()) for w in ctx.P.get("exclude_title_words", [])):
        return False
    if (ctx.P.get("relocation") or {}).get("enabled"):
        return True
    return geo_check(loc, "", None)[0]


def _gh(ctx, token):
    out = []
    data = http(f"https://boards-api.greenhouse.io/v1/boards/{token}/jobs")
    for r in data.get("jobs", []):
        jid = f"greenhouse:{token}:{r['id']}"
        loc = (r.get("location") or {}).get("name", "")
        if ctx.seen(jid) or not _title_geo_prefilter(ctx, r["title"], loc):
            continue
        try:
            d = http(f"https://boards-api.greenhouse.io/v1/boards/{token}/jobs/{r['id']}?pay_transparency=true")
        except Exception:
            d = {}
        sal = None
        for pr in d.get("pay_input_ranges") or []:
            if pr.get("min_cents") and pr.get("max_cents"):
                lo, hi = pr["min_cents"] / 100, pr["max_cents"] / 100
                sal = dict(min=lo, max=hi, cur=(pr.get("currency_type") or "USD").upper(), per="hour" if hi < 1000 else "year")
                break
        out.append(J(f"greenhouse:{token}", r["id"], r["title"], r.get("company_name") or token, r.get("absolute_url"),
                     iso_epoch(r.get("first_published") or r.get("updated_at")), loc,
                     True if "remote" in loc.lower() or "anywhere" in loc.lower() else None, "",
                     clean(d.get("content")), sal))
        out[-1]["id"] = jid
    return out


def _lever(ctx, token):
    out = []
    for r in http(f"https://api.lever.co/v0/postings/{token}?mode=json"):
        cat = r.get("categories") or {}
        loc = cat.get("location") or ", ".join(cat.get("allLocations") or [])
        wt = (r.get("workplaceType") or "").lower()
        sr = r.get("salaryRange") or {}
        sal = None
        if sr.get("min") and sr.get("max"):
            iv = (sr.get("interval") or "").lower()
            sal = dict(min=float(sr["min"]), max=float(sr["max"]), cur=(sr.get("currency") or "USD").upper(),
                       per="hour" if "hour" in iv else ("month" if "month" in iv else "year"))
        j = J(f"lever:{token}", r["id"], r.get("text"), token, r.get("hostedUrl"), to_epoch(r.get("createdAt")), loc,
              True if wt == "remote" or "remote" in loc.lower() else (False if wt in ("onsite", "hybrid") else None),
              cat.get("commitment", ""), (r.get("descriptionPlain") or "") + " " + (r.get("additionalPlain") or ""), sal)
        j["id"] = f"lever:{token}:{r['id']}"
        out.append(j)
    return out


def _ashby(ctx, token):
    out = []
    for r in http(f"https://api.ashbyhq.com/posting-api/job-board/{token}?includeCompensation=true").get("jobs", []):
        if r.get("isListed") is False:
            continue
        comp = r.get("compensation") or {}
        sal = None
        for c in comp.get("summaryComponents") or []:
            if (c.get("compensationType") or "").lower() == "salary" and c.get("minValue") and c.get("maxValue"):
                iv = (c.get("interval") or "").lower()
                sal = dict(min=float(c["minValue"]), max=float(c["maxValue"]), cur=(c.get("currencyCode") or "USD").upper(),
                           per="hour" if "hour" in iv else ("month" if "month" in iv else "year"))
                break
        loc = r.get("location") or ""
        sec = ", ".join(s.get("location", "") if isinstance(s, dict) else str(s) for s in (r.get("secondaryLocations") or []))
        j = J(f"ashby:{token}", r["id"], r.get("title"), token, r.get("jobUrl") or r.get("applyUrl"), iso_epoch(r.get("publishedAt")),
              loc + (", " + sec if sec else ""), True if r.get("isRemote") else (False if r.get("workplaceType") in ("OnSite", "Hybrid") else None),
              r.get("employmentType", ""), r.get("descriptionPlain") or "", sal, comp.get("compensationTierSummary") or "")
        j["id"] = f"ashby:{token}:{r['id']}"
        out.append(j)
    return out


def _workable(ctx, token):
    out = []
    d = http(f"https://apply.workable.com/api/v1/widget/accounts/{token}?details=true")
    for r in d.get("jobs", []):
        loc = ", ".join(x for x in (r.get("city"), r.get("state"), r.get("country")) if x)
        remote = True if r.get("telecommuting") else None
        j = J(f"workable:{token}", r.get("shortcode"), r.get("title"), d.get("name") or token, r.get("url") or r.get("shortlink"),
              iso_epoch(r.get("published_on") or r.get("created_at")), loc or ("Remote" if remote else ""), remote,
              r.get("employment_type", ""), clean(r.get("description")))
        j["id"] = f"workable:{token}:{r.get('shortcode')}"
        out.append(j)
    return out


def _recruitee(ctx, token):
    out = []
    for r in http(f"https://{token}.recruitee.com/api/offers/").get("offers", []):
        loc = r.get("location") or ", ".join(x for x in (r.get("city"), r.get("country")) if x)
        j = J(f"recruitee:{token}", r["id"], r.get("title"), r.get("company_name") or token, r.get("careers_url"),
              iso_epoch(r.get("published_at") or r.get("created_at")), loc,
              True if (r.get("remote") or r.get("on_site") is False and r.get("hybrid") is False) else None,
              r.get("employment_type_code", ""), clean((r.get("description") or "") + " " + (r.get("requirements") or "")))
        j["id"] = f"recruitee:{token}:{r['id']}"
        out.append(j)
    return out


def f_ats(ctx):
    cf = HOME / "companies.json"
    boards = json.loads(cf.read_text(encoding="utf-8")) if cf.exists() else {}
    tasks = [(fn, ctx, t) for key, fn in (("greenhouse", _gh), ("lever", _lever), ("ashby", _ashby), ("workable", _workable), ("recruitee", _recruitee)) for t in boards.get(key, [])]
    out, dead = [], []

    def run(a):
        fn, c, t = a
        try:
            return fn(c, t)
        except urllib.error.HTTPError as e:
            if e.code == 404:
                dead.append(f"{fn.__name__}:{t}")
            return []
        except Exception as e:
            log.debug("ats %s %s: %s", fn.__name__, t, e)
            return []
    with ThreadPoolExecutor(8) as ex:
        for res in ex.map(run, tasks):
            out.extend(res)
    if dead:
        log.info("ats: %d boards 404 (remove from companies.json): %s", len(dead), ", ".join(dead[:15]))
    return out


SOURCES = {"remoteok": f_remoteok, "remotive": f_remotive, "jobicy": f_jobicy, "himalayas": f_himalayas,
           "workingnomads": f_workingnomads, "arbeitnow": f_arbeitnow, "wwr": f_wwr, "hn_jobs": f_hn_jobs, "hn_hiring": f_hn_hiring,
           "remoterocketship": f_remoterocketship, "ats": f_ats}

# ----------------------------------------------------------------- storage
class DB:
    def __init__(self):
        HOME.mkdir(parents=True, exist_ok=True)
        self.c = sqlite3.connect(HOME / "state.sqlite", check_same_thread=False)
        self.c.executescript("""CREATE TABLE IF NOT EXISTS seen(id TEXT PRIMARY KEY, ts INT);
        CREATE TABLE IF NOT EXISTS alerted(fp TEXT PRIMARY KEY, id TEXT, ts INT, score INT, job TEXT);
        CREATE TABLE IF NOT EXISTS meta(k TEXT PRIMARY KEY, v TEXT);""")
        self.lock = threading.Lock()
        for col in ("ckey", "src"):
            try:
                self.c.execute(f"ALTER TABLE alerted ADD COLUMN {col} TEXT")
            except sqlite3.OperationalError:
                pass
        for fp, jb in self.c.execute("SELECT fp, job FROM alerted WHERE src IS NULL").fetchall():
            self.c.execute("UPDATE alerted SET src=? WHERE fp=?", (json.loads(jb)["source"].split(":")[0], fp))
        for fp, jb in self.c.execute("SELECT fp, job FROM alerted WHERE ckey IS NULL").fetchall():
            self.c.execute("UPDATE alerted SET ckey=? WHERE fp=?", (company_key(json.loads(jb)), fp))
        self.c.commit()

    def source_count(self, src, hours=24):
        with self.lock:
            return self.c.execute("SELECT COUNT(*) FROM alerted WHERE src=? AND ts>?", (src, time.time() - hours * 3600)).fetchone()[0]

    def company_count(self, ck, days):
        with self.lock:
            return self.c.execute("SELECT COUNT(*) FROM alerted WHERE ckey=? AND ts>?", (ck, time.time() - days * 86400)).fetchone()[0]

    def seen(self, jid):
        with self.lock:
            return self.c.execute("SELECT 1 FROM seen WHERE id=?", (jid,)).fetchone() is not None

    def mark(self, jid):
        with self.lock:
            self.c.execute("INSERT OR IGNORE INTO seen VALUES(?,?)", (jid, int(time.time())))
            self.c.commit()

    def meta(self, k, v=None):
        with self.lock:
            if v is None:
                r = self.c.execute("SELECT v FROM meta WHERE k=?", (k,)).fetchone()
                return r[0] if r else None
            self.c.execute("INSERT OR REPLACE INTO meta VALUES(?,?)", (k, str(v)))
            self.c.commit()

    def alerted(self, fp):
        with self.lock:
            return self.c.execute("SELECT 1 FROM alerted WHERE fp=?", (fp,)).fetchone() is not None

    def add_alert(self, fp, job, score):
        with self.lock:
            self.c.execute("INSERT OR REPLACE INTO alerted(fp,id,ts,score,job,ckey,src) VALUES(?,?,?,?,?,?,?)",
                           (fp, job["id"], int(time.time()), score, json.dumps(job), company_key(job), job["source"].split(":")[0]))
            self.c.commit()

# ----------------------------------------------------------------- telegram
def tg_call(cfg, method, payload):
    tok = os.environ.get("JOBSEARCH_TG_TOKEN") or cfg.get("telegram", {}).get("bot_token")
    if not tok:
        raise SystemExit("Telegram bot_token missing. Put it in ~/.job-search/config.json or env JOBSEARCH_TG_TOKEN")
    for _ in range(3):
        try:
            return http(f"https://api.telegram.org/bot{tok}/{method}", {"Content-Type": "application/json"},
                        json.dumps(payload).encode(), timeout=30)
        except urllib.error.HTTPError as e:
            body = e.read().decode("utf-8", "replace")
            if e.code == 429:
                time.sleep(int(re.search(r"retry_after\D+(\d+)", body).group(1)) + 1 if "retry_after" in body else 5)
                continue
            raise RuntimeError(f"telegram {e.code}: {body[:200]}")
    raise RuntimeError("telegram rate-limited")


def tg_send(cfg, text, url=None):
    chat = os.environ.get("JOBSEARCH_TG_CHAT") or cfg.get("telegram", {}).get("chat_id")
    if not chat:
        raise SystemExit("Telegram chat_id missing. Run: jobsearch.py tg-chat-id")
    payload = {"chat_id": chat, "text": text, "parse_mode": "HTML", "disable_web_page_preview": True}
    if url and url.startswith("http"):
        payload["reply_markup"] = {"inline_keyboard": [[{"text": "Apply now ▶", "url": url}]]}
    return tg_call(cfg, "sendMessage", payload)


def fmt_msg(job, ev):
    e = html.escape
    sal = job.get("_sal")
    reloc = job.get("_mode") == "reloc"
    need, mine = job.get("_need"), job.get("_mine", 4)
    if need is None:
        exp = "not stated"
    else:
        exp = f"{need}+ yrs asked · you ~{mine} " + ("✅" if need <= mine else "⚠️")
    pretty = []
    for r in ev["reasons"]:
        if r.startswith("title~"):
            r = "Title matches: " + r[6:]
        elif r.startswith("skills: "):
            r = "Skills hit: " + r[8:]
        pretty.append(r[:1].upper() + r[1:])
    src = job["source"].split(":")[0] + (" · " + job["source"].split(":")[1] if ":" in job["source"] else "")
    lines = [
        f"{ev['tier']} <b>{e(job['title'])}</b>",
        f"🏢 <b>{e(job['company'] or '?')}</b>  ·  " + ("✈️ RELOCATE + VISA" if reloc else "🌍 REMOTE"),
        "",
        f"<b>📍 Location:</b> {e(job['location'] or 'Remote')}",
        f"<b>💼 Type:</b> {e(job['employment'] or 'not stated')}",
        f"<b>💰 Pay:</b> {e(fmt_sal(sal))}",
        f"<b>🧠 Experience:</b> {e(exp)}",
        f"<b>🕒 Posted:</b> {e(when_str(job.get('posted')))}",
        f"<b>📡 Source:</b> {e(src)}   <b>🎯 Score:</b> {ev['score']}/100",
        "",
        "<b>✅ Why it fits</b>",
    ] + ["• " + e(r) for r in pretty]
    if ev["flags"]:
        lines += ["", "<b>⚠️ Check before applying</b>"] + ["• " + e(f) for f in ev["flags"]]
    lines += ["", f"<code>{e(job['id'])}</code>"]
    return "\n".join(lines)


def company_key(job):
    return re.sub(r"[^a-z0-9]", "", (job.get("company") or "").split(":")[0].lower())


def fingerprint(job):
    n = lambda s: re.sub(r"[^a-z0-9]", "", s.lower())
    return hashlib.sha1((n(job["company"].split(":")[0]) + "|" + n(job["title"])).encode()).hexdigest()

# ----------------------------------------------------------------- config
def load_json(p, default):
    try:
        return json.loads(Path(p).read_text(encoding="utf-8"))
    except FileNotFoundError:
        return default


def cmd_init(a=None):
    HOME.mkdir(parents=True, exist_ok=True)
    for name in ("config.json", "profile.json", "companies.json"):
        dst, src = HOME / name, SKILL_DIR / "references" / name.replace(".json", ".template.json")
        if not dst.exists():
            dst.write_text(src.read_text(encoding="utf-8"), encoding="utf-8")
            print("created", dst)
        else:
            print("exists ", dst)
    print("\nNext: edit config.json (telegram), profile.json (from resume), then `jobsearch.py tg-test` and `jobsearch.py run --dry-run`")

# ----------------------------------------------------------------- pipeline
def process(jobs, P, C, db, label, first_run, dry, max_age_s, sink, ignore_seen=False):
    """Evaluate unseen jobs; sink(job, ev) delivers. Returns stats."""
    st = dict(new=0, match=0, sent=0)
    cands, batch_fp = [], set()
    for j in jobs:
        if not j.get("id") or (db.seen(j["id"]) and not ignore_seen):
            continue
        st["new"] += 1
        if first_run and not j.get("posted"):
            if not dry: db.mark(j["id"])
            continue
        ev = evaluate(j, P, C)
        limit = SOURCE_MAX_AGE_H.get(j["source"], 0) * 3600 or max_age_s
        if ev["ok"] and j.get("posted") and time.time() - j["posted"] > limit:
            ev = dict(ev, ok=False, reject="too old")
        if not ev["ok"]:
            if not dry: db.mark(j["id"])
            log.debug("skip %s | %s | %s", j["id"], j["title"], ev["reject"])
            continue
        fp = fingerprint(j)
        if db.alerted(fp) or fp in batch_fp:
            if not dry: db.mark(j["id"])
            continue
        batch_fp.add(fp)
        cands.append((ev["score"], j, ev))
    st["match"] = len(cands)
    cap, win = C.get("max_per_company", 2), C.get("company_window_days", 30)
    batch_ck, batch_src, sent_n = {}, {}, 0
    for _, j, ev in sorted(cands, key=lambda x: -x[0]):
        if sent_n >= C.get("max_alerts_per_cycle", 25):
            break
        ck = company_key(j)
        if ck and cap and db.company_count(ck, win) + batch_ck.get(ck, 0) >= cap:
            if not dry: db.mark(j["id"])
            log.debug("cap: %s already has %d alerts", ck, cap)
            continue
        src = j["source"].split(":")[0]
        scap = C.get("max_per_source_day", 8)
        if scap and db.source_count(src) + batch_src.get(src, 0) >= scap:
            if not dry: db.mark(j["id"])
            log.debug("source cap: %s", src)
            continue
        batch_src[src] = batch_src.get(src, 0) + 1
        batch_ck[ck] = batch_ck.get(ck, 0) + 1
        sent_n += 1
        try:
            sink(j, ev)
        except Exception as e:
            log.error("deliver failed %s: %s", j["id"], e)
            batch_ck[ck] -= 1; batch_src[src] -= 1; sent_n -= 1
            continue
        if not dry:
            db.mark(j["id"]); db.add_alert(fingerprint(j), j, ev["score"])
        st["sent"] += 1
        time.sleep(1.1)
    return st


def run_cycle(C, P, db, dry=False, only=None, max_age_min=None, backfill=False):
    max_age_s = (max_age_min or C.get("max_age_minutes", 360)) * 60
    enabled = {k: v for k, v in C.get("sources", {k: True for k in SOURCES}).items() if v}
    intervals = {**DEFAULT_INTERVALS, **C.get("source_interval_min", {})}
    total = dict(new=0, match=0, sent=0)

    def sink(j, ev):
        msg = fmt_msg(j, ev)
        if dry:
            print("\n--- WOULD ALERT ---\n" + re.sub(r"</?[a-z]+>", "", html.unescape(msg)) + f"\n{j['url']}")
        else:
            tg_send(C, msg, j["url"])

    ctx = Ctx(P, C, db.seen)
    for name, fn in SOURCES.items():
        if only and name not in only or (not only and name not in enabled):
            continue
        last = float(db.meta("last:" + name) or 0)
        if not only and not backfill and time.time() - last < intervals.get(name, C.get("poll_interval_min", 5)) * 60 - 20:
            continue
        t0 = time.time()
        try:
            jobs = fn(ctx)
        except Exception as e:
            n = int(db.meta("fail:" + name) or 0) + 1
            db.meta("fail:" + name, n)
            log.warning("source %s failed (%d in a row): %s", name, n, e)
            continue
        db.meta("fail:" + name, 0)
        if not dry:
            db.meta("last:" + name, time.time())
        first = db.meta("base:" + name) is None
        st = process(jobs, P, C, db, name, first and not backfill, dry, max_age_s, sink, ignore_seen=backfill)
        if not dry:
            db.meta("base:" + name, 1)
        log.info("%-16s fetched=%-4d new=%-4d match=%-3d sent=%-3d %.1fs%s", name, len(jobs), st["new"], st["match"], st["sent"],
                 time.time() - t0, " (baseline)" if first else "")
        for k in total: total[k] += st[k]
    return total


def cmd_run(a):
    C, P, db = load_json(HOME / "config.json", {}), load_json(HOME / "profile.json", {}), DB()
    if not P.get("target_titles"):
        raise SystemExit("profile.json has no target_titles. Run `init` and fill the profile.")
    only = a.sources.split(",") if a.sources else None
    t = run_cycle(C, P, db, a.dry_run, only, a.max_age_min, a.backfill)
    print("cycle:", t)
    hb = C.get("heartbeat_hours", 24)
    if hb and not a.dry_run and not only:  # one-shot (cloud cron) mode heartbeat
        last = float(db.meta("last_hb") or 0)
        if not last:
            db.meta("last_hb", time.time())
        elif time.time() - last > hb * 3600:
            fails = {n: db.meta("fail:" + n) for n in SOURCES if int(db.meta("fail:" + n) or 0) > 5}
            tg_send(C, f"💓 job-search alive (cloud). last cycle: {t}" + (f"\n⚠ failing sources: {fails}" if fails else ""))
            db.meta("last_hb", time.time())


def cmd_daemon(a):
    s = socket.socket()
    try:
        s.bind(("127.0.0.1", LOCK_PORT))
    except OSError:
        raise SystemExit("daemon already running")
    log.info("daemon start; home=%s", HOME)
    last_hb = 0
    while True:
        try:
            C, P, db = load_json(HOME / "config.json", {}), load_json(HOME / "profile.json", {}), DB()  # hot-reload edits
            t = run_cycle(C, P, db)
            hb = C.get("heartbeat_hours", 24)
            if hb and time.time() - last_hb > hb * 3600:
                if last_hb:
                    fails = {n: db.meta("fail:" + n) for n in SOURCES if int(db.meta("fail:" + n) or 0) > 5}
                    tg_send(C, f"💓 job-search alive. last cycle: {t}" + (f"\n⚠ failing sources: {fails}" if fails else ""))
                last_hb = time.time()
        except SystemExit:
            raise
        except Exception as e:
            log.exception("cycle error: %s", e)
        time.sleep(C.get("poll_interval_min", 5) * 60 + random.randint(0, 20))


def cmd_ingest(a):
    C, P, db = load_json(HOME / "config.json", {}), load_json(HOME / "profile.json", {}), DB()
    raw = json.load(sys.stdin if a.file == "-" else open(a.file, encoding="utf-8"))
    jobs = []
    for r in raw if isinstance(raw, list) else raw.get("jobs", []):
        src = "ingest:" + (r.get("source") or a.label)
        jid = r.get("id") or hashlib.sha1((r.get("url") or r.get("title", "")).encode()).hexdigest()[:16]
        j = J(src, jid, r.get("title"), r.get("company"), r.get("url"), to_epoch(r.get("posted")) or time.time(),
              r.get("location", ""), r.get("remote", True), r.get("employment", ""), r.get("text") or r.get("description", ""),
              None, r.get("salary_text") or r.get("salary", ""))
        j["id"] = f"{src}:{jid}"
        jobs.append(j)
    sink = (lambda j, ev: print(fmt_msg(j, ev))) if a.dry_run else (lambda j, ev: tg_send(C, fmt_msg(j, ev), j["url"]))
    st = process(jobs, P, C, db, "ingest", False, a.dry_run, (C.get("max_age_minutes", 360)) * 60 * 8, sink)
    print("ingest:", len(jobs), "jobs ->", st)


def cmd_status(a):
    db = DB()
    n = lambda q: db.c.execute(q).fetchone()[0]
    print("seen:", n("SELECT COUNT(*) FROM seen"), "alerted:", n("SELECT COUNT(*) FROM alerted"))
    for name in SOURCES:
        last = db.meta("last:" + name)
        print(f"  {name:<16} last={age_str(float(last)) if last else 'never':<12} fails={db.meta('fail:' + name) or 0}")


def cmd_show(a):
    r = DB().c.execute("SELECT job FROM alerted WHERE id=?", (a.id,)).fetchone()
    if not r:
        raise SystemExit("not found")
    j = json.loads(r[0])
    print(f"{j['title']} @ {j['company']}\n{j['url']}\n{j['location']} | {j['employment']} | {j.get('sal_text')}\n\n{j['text']}")


ATS_PATTERNS = {
    "greenhouse": re.compile(r"(?:boards|job-boards)(?:\.eu)?\.greenhouse\.io/(?:embed/job_board\?for=)?([A-Za-z0-9_-]{2,40})", re.I),
    "lever": re.compile(r"jobs(?:\.eu)?\.lever\.co/([A-Za-z0-9_-]{2,40})", re.I),
    "ashby": re.compile(r"jobs\.ashbyhq\.com/([A-Za-z0-9_.-]{2,40})", re.I),
    "workable": re.compile(r"apply\.workable\.com/([A-Za-z0-9_-]{2,40})", re.I),
    "recruitee": re.compile(r"https?://([a-z0-9-]{2,40})\.recruitee\.com", re.I),
}
ATS_PROBE = {
    "greenhouse": lambda t: f"https://boards-api.greenhouse.io/v1/boards/{t}/jobs",
    "lever": lambda t: f"https://api.lever.co/v0/postings/{t}?mode=json",
    "ashby": lambda t: f"https://api.ashbyhq.com/posting-api/job-board/{t}",
    "workable": lambda t: f"https://apply.workable.com/api/v1/widget/accounts/{t}",
    "recruitee": lambda t: f"https://{t}.recruitee.com/api/offers/",
}


def probe_board(kind, token):
    try:
        d = http(ATS_PROBE[kind](token), timeout=20)
        return len(d.get("jobs", d.get("offers", []))) if isinstance(d, dict) else len(d)
    except Exception:
        return -1


def cmd_discover(a):
    """Harvest ATS board slugs from every job URL/description we can see + optional candidate file, probe, add live ones."""
    C, P = load_json(HOME / "config.json", {}), load_json(HOME / "profile.json", {})
    ctx = Ctx(P, C, lambda x: False)
    blob = []
    for name, fn in SOURCES.items():
        if name == "ats":
            continue
        try:
            for j in fn(ctx):
                blob.append(f"{j.get('url') or ''} {j.get('text') or ''}")
        except Exception as e:
            log.warning("discover %s: %s", name, e)
    found = {k: set() for k in ATS_PATTERNS}
    text = "\n".join(blob)
    for kind, rx in ATS_PATTERNS.items():
        found[kind] |= {m.lower() for m in rx.findall(text)}
    if a.candidates:
        for line in Path(a.candidates).read_text(encoding="utf-8").split():
            for kind in ATS_PATTERNS:
                found[kind].add(line.strip().lower())
    cf = HOME / "companies.json"
    boards = load_json(cf, {})
    tasks = [(k, t) for k, ts in found.items() for t in ts if t not in boards.get(k, [])]
    log.info("discover: probing %d candidate boards", len(tasks))
    with ThreadPoolExecutor(48) as ex:
        res = list(ex.map(lambda x: (x[0], x[1], probe_board(*x)), tasks))
    added = {}
    for k, t, n in res:
        if n > 0:
            boards.setdefault(k, []).append(t)
            added.setdefault(k, []).append(f"{t}({n})")
    for k, v in added.items():
        print(f"+{len(v)} {k}: {', '.join(v)}")
    if not a.dry_run:
        cf.write_text(json.dumps(boards, indent=2), encoding="utf-8")
    print({k: len(v) for k, v in boards.items() if isinstance(v, list)})


def cmd_tg_chat_id(a):
    C = load_json(HOME / "config.json", {})
    r = tg_call(C, "getUpdates", {})
    seen = {(u.get("message") or u.get("channel_post") or {}).get("chat", {}).get("id") for u in r.get("result", [])}
    seen.discard(None)
    print("chat ids:", seen or "none - send any message to your bot in Telegram, then rerun")


def cmd_tg_test(a):
    C = load_json(HOME / "config.json", {})
    tg_send(C, "✅ <b>job-search</b> connected. Alerts will land here.", "https://example.com")
    print("sent")


def main():
    setup_logging()
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sp = ap.add_subparsers(dest="cmd", required=True)
    sp.add_parser("init").set_defaults(fn=cmd_init)
    sp.add_parser("tg-chat-id").set_defaults(fn=cmd_tg_chat_id)
    sp.add_parser("tg-test").set_defaults(fn=cmd_tg_test)
    sp.add_parser("status").set_defaults(fn=cmd_status)
    sp.add_parser("daemon").set_defaults(fn=cmd_daemon)
    r = sp.add_parser("run"); r.set_defaults(fn=cmd_run)
    r.add_argument("--dry-run", action="store_true"); r.add_argument("--sources"); r.add_argument("--max-age-min", type=int)
    r.add_argument("--backfill", action="store_true", help="re-evaluate already-seen jobs (use with --max-age-min)")
    i = sp.add_parser("ingest"); i.set_defaults(fn=cmd_ingest)
    i.add_argument("file"); i.add_argument("--label", default="sweep"); i.add_argument("--dry-run", action="store_true")
    d = sp.add_parser("discover"); d.set_defaults(fn=cmd_discover); d.add_argument("--candidates"); d.add_argument("--dry-run", action="store_true")
    s = sp.add_parser("show"); s.set_defaults(fn=cmd_show); s.add_argument("id")
    a = ap.parse_args()
    a.fn(a)


if __name__ == "__main__":
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    main()
