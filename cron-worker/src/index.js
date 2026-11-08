// Pings the GitHub workflow every 5 minutes (GitHub's own cron is heavily delayed on free repos).
// Secret GH_TOKEN = fine-grained PAT, repo jobwatch only, permission: Actions (read & write).
const URL = "https://api.github.com/repos/Anand1405/jobwatch/actions/workflows/job-search.yml/dispatches";

async function dispatch(env) {
  const r = await fetch(URL, {
    method: "POST",
    headers: {
      Authorization: `Bearer ${env.GH_TOKEN}`,
      Accept: "application/vnd.github+json",
      "User-Agent": "jobwatch-cron",
      "X-GitHub-Api-Version": "2022-11-28",
    },
    body: JSON.stringify({ ref: "main", inputs: { backfill_hours: "0" } }),
  });
  if (!r.ok) console.log("dispatch failed", r.status, await r.text());
  return r.status;
}

export default {
  async scheduled(event, env, ctx) { ctx.waitUntil(dispatch(env)); },
  async fetch() { return new Response("jobwatch cron ok"); },
};
