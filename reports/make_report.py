"""Render the overnight HTML report from run data plus a few hand-written notes.

Usage: python reports/make_report.py OUT.html NOTES.json RUN_ID [RUN_ID ...]
"""
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from collect import run_data  # noqa: E402

TEMPLATE = r"""<title>Evolve Overnight</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Fraunces:opsz,wght@9..144,400;9..144,600&family=Public+Sans:wght@400;600&family=JetBrains+Mono:wght@400;500&display=swap">
<style>
/* Layout: a lab notebook. One reading column, charts drawn on graph-paper panels. */
:root {
  --bg: #f6f4ee; --panel: #fffdf8; --fg: #1d2330; --dim: #6a7183; --line: #ddd8cc; --grid: #ebe6da;
  --a: #c2672b; --b: #2f6f8f; --good: #2e7d4f; --fog: #cfd4dc;
  --display: "Fraunces", Georgia, serif; --body: "Public Sans", system-ui, sans-serif; --mono: "JetBrains Mono", ui-monospace, monospace;
}
@media (prefers-color-scheme: dark) { :root:not([data-theme="light"]) {
  --bg: #12151c; --panel: #181c25; --fg: #e9e6de; --dim: #949bab; --line: #2b3140; --grid: #20252f;
  --a: #e3955c; --b: #74b3d3; --good: #6cc391; --fog: #39404f; color-scheme: dark } }
:root[data-theme="dark"] {
  --bg: #12151c; --panel: #181c25; --fg: #e9e6de; --dim: #949bab; --line: #2b3140; --grid: #20252f;
  --a: #e3955c; --b: #74b3d3; --good: #6cc391; --fog: #39404f; color-scheme: dark }
html, body { background: var(--bg); color: var(--fg); }
body { font: 16px/1.6 var(--body); }
.wrap { max-width: 860px; margin: 0 auto; padding-inline: 18px; padding-block: 48px 72px; display: grid; gap: 34px; }
h1 { font: 600 clamp(2.2rem, 6vw, 3.6rem)/1.05 var(--display); margin: 0; text-wrap: balance; }
h2 { font: 600 1.6rem/1.15 var(--display); margin: 0; text-wrap: balance; }
p { margin: 0; max-width: 64ch; }
.eyebrow { font: 500 .75rem/1 var(--mono); letter-spacing: .12em; text-transform: uppercase; color: var(--dim); margin: 0; }
section { display: grid; gap: 14px; }
.panel { background: var(--panel); border: 1px solid var(--line); border-radius: 12px; padding: 16px;
  background-image: linear-gradient(var(--grid) 1px, transparent 1px), linear-gradient(90deg, var(--grid) 1px, transparent 1px);
  background-size: 24px 24px; }
.stats { display: grid; grid-template-columns: repeat(auto-fit, minmax(150px, 1fr)); gap: 12px; }
.stat { background: var(--panel); border: 1px solid var(--line); border-radius: 10px; padding: 12px 14px; }
.stat b { display: block; font: 600 1.7rem/1.1 var(--display); font-variant-numeric: tabular-nums; }
.stat span { color: var(--dim); font-size: .85rem; }
svg text { fill: var(--dim); font: 11px var(--mono); }
.cases { display: grid; gap: 16px; }
.case { display: grid; gap: 6px; }
.case-head { display: flex; flex-wrap: wrap; justify-content: space-between; gap: 4px 12px; font-size: .95rem; }
.case-head .id { font: 500 .85rem var(--mono); }
.tag { font: 500 .72rem var(--mono); padding: 2px 8px; border-radius: 999px; border: 1px solid var(--line); color: var(--dim); }
.tag.hit { color: var(--good); border-color: var(--good); }
.tag.new { color: #fff; background: var(--a); border-color: var(--a); }
.bar { position: relative; height: 18px; border-radius: 5px; background: var(--fog); overflow: hidden; }
.bar .best { position: absolute; inset: 0 auto 0 0; background: linear-gradient(90deg, var(--a), var(--b)); }
.bar .rec { position: absolute; top: -2px; bottom: -2px; width: 2px; background: var(--fg); }
.nums { display: flex; justify-content: space-between; font: .8rem var(--mono); color: var(--dim); font-variant-numeric: tabular-nums; }
.calib { display: flex; flex-wrap: wrap; gap: 8px; }
ul.notes { margin: 0; padding-left: 1.2em; display: grid; gap: 6px; max-width: 64ch; }
.mono { font-family: var(--mono); font-size: .9em; }
.legend { display: flex; flex-wrap: wrap; gap: 6px 18px; font-size: .85rem; color: var(--dim); }
.sw { display: inline-block; width: 18px; height: 3px; vertical-align: middle; margin-right: 6px; }
</style>

<div class="wrap">
  <header style="display:grid;gap:14px">
    <p class="eyebrow" id="when"></p>
    <h1 id="headline"></h1>
    <p id="lede"></p>
  </header>
  <div class="stats" id="stats"></div>

  <section>
    <h2>Fitness, round by round</h2>
    <p>Average score across all cases (1.0 = matching every known record). The pilot ran on the first 13 cases; run 2 added bigger targets and started from the pilot's best programs, so its scale starts lower.</p>
    <div class="legend"><span><i class="sw" style="background:var(--a)"></i>best so far</span><span><i class="sw" style="background:var(--b)"></i>best in that round</span></div>
    <div class="panel"><svg id="fit" viewBox="0 0 800 260" width="100%" role="img" aria-label="Fitness over generations"></svg></div>
  </section>

  <section>
    <h2>The targets</h2>
    <p>Each bar runs to the proven ceiling. The colored part is the best graph the engine has built. The dark tick is the best known record.</p>
    <div class="cases" id="targets"></div>
  </section>

  <section>
    <h2>Calibration: known answers it had to rediscover</h2>
    <div class="calib" id="calib"></div>
  </section>

  <section>
    <h2>What Haiku came up with</h2>
    <ul class="notes" id="ideas"></ul>
  </section>

  <section>
    <h2>Cost</h2>
    <div class="stats" id="cost"></div>
    <p class="mono" id="costnote" style="color:var(--dim)"></p>
  </section>

  <section>
    <h2>Cloud</h2>
    <p id="cloud"></p>
  </section>

  <section>
    <h2>What I'd do next</h2>
    <ul class="notes" id="next"></ul>
  </section>
</div>

<script>
const DATA = __DATA__;
const NOTES = __NOTES__;
const runs = Object.values(DATA);
const last = runs[runs.length - 1];
const $ = id => document.getElementById(id);
$("when").textContent = NOTES.when;
$("headline").textContent = NOTES.headline;
$("lede").textContent = NOTES.lede;
NOTES.ideas.forEach(t => { const li = document.createElement("li"); li.textContent = t; $("ideas").appendChild(li); });
NOTES.next.forEach(t => { const li = document.createElement("li"); li.textContent = t; $("next").appendChild(li); });
$("cloud").textContent = NOTES.cloud;

const totalCalls = runs.reduce((s, r) => s + r.calls, 0);
const totalGens = runs.reduce((s, r) => s + Math.max(0, r.generations.length - 1), 0);
const stat = (el, v, l) => { const d = document.createElement("div"); d.className = "stat"; d.innerHTML = `<b></b><span></span>`; d.querySelector("b").textContent = v; d.querySelector("span").textContent = l; $(el).appendChild(d); };
const bbc = last.best_by_case;
const recs = NOTES.cases.filter(c => c.kind === "target");
const beaten = recs.filter(c => (bbc[c.id]?.value || 0) > c.record).length;
const tied = recs.filter(c => (bbc[c.id]?.value || 0) === c.record).length;
stat("stats", totalGens, "rounds of evolution");
stat("stats", totalCalls, "Haiku programs written");
stat("stats", `${NOTES.cases.filter(c => c.kind === "calibration" && (bbc[c.id]?.value || 0) >= c.record).length}/${NOTES.cases.filter(c => c.kind === "calibration").length}`, "known answers rediscovered");
stat("stats", beaten ? `${beaten} new` : (tied ? `${tied} tied` : "none yet"), "records beaten");

// fitness chart: runs laid end to end
const pts = []; let x0 = 0;
runs.forEach(r => { r.generations.forEach(g => pts.push({ x: x0 + g.g, best: g.best, gb: g.gen_best ?? g.best, run: r.run_id })); x0 += r.generations.length; });
const svg = $("fit"), W = 800, H = 260, L = 44, R = 12, T = 12, B = 30;
const ys = pts.flatMap(p => [p.best, p.gb]).filter(v => v != null);
const ymin = Math.floor(Math.min(...ys) * 20) / 20, ymax = Math.min(1.02, Math.ceil(Math.max(...ys) * 20) / 20 + 0.02);
const sx = x => L + (x / Math.max(1, x0 - 1)) * (W - L - R), sy = y => T + (1 - (y - ymin) / (ymax - ymin)) * (H - T - B);
let s = "";
for (let y = ymin; y <= ymax + 1e-9; y += 0.05) s += `<line x1="${L}" x2="${W - R}" y1="${sy(y)}" y2="${sy(y)}" stroke="var(--line)"/><text x="${L - 6}" y="${sy(y) + 4}" text-anchor="end">${y.toFixed(2)}</text>`;
let xx = 0; runs.forEach(r => { s += `<text x="${sx(xx)}" y="${H - 8}">${r.run_id}</text>`; if (xx) s += `<line x1="${sx(xx) - 4}" x2="${sx(xx) - 4}" y1="${T}" y2="${H - B}" stroke="var(--dim)" stroke-dasharray="3 4"/>`; xx += r.generations.length; });
const path = k => pts.map((p, i) => `${i ? "L" : "M"}${sx(p.x).toFixed(1)},${sy(p[k]).toFixed(1)}`).join("");
s += `<path d="${path("gb")}" fill="none" stroke="var(--b)" stroke-width="1.5" opacity=".8"/>`;
s += `<path d="${path("best")}" fill="none" stroke="var(--a)" stroke-width="2.5"/>`;
const e = pts[pts.length - 1]; s += `<circle cx="${sx(e.x)}" cy="${sy(e.best)}" r="4" fill="var(--a)"/><text x="${sx(e.x) - 6}" y="${sy(e.best) - 8}" text-anchor="end" style="fill:var(--fg)">${e.best.toFixed(3)}</text>`;
svg.innerHTML = s;

// targets
recs.forEach(c => {
  const v = bbc[c.id]?.value || 0, start = (last.case_history[c.id] || [])[0]?.[1] || 0;
  const d = document.createElement("div"); d.className = "case";
  const tag = v > c.record ? `<span class="tag new">NEW RECORD</span>` : v === c.record ? `<span class="tag hit">ties record</span>` : `<span class="tag">${Math.round(100 * v / c.record)}% of record</span>`;
  d.innerHTML = `<div class="case-head"><span><span class="id">${c.id}</span> &nbsp;degree ${c.d}, everyone within ${c.D} steps</span>${tag}</div>
    <div class="bar" role="img" aria-label="best ${v}, record ${c.record}, ceiling ${c.ceiling}"><div class="best" style="width:${100 * v / c.ceiling}%"></div><div class="rec" style="left:${100 * c.record / c.ceiling}%"></div></div>
    <div class="nums"><span>start ${start} → best <b style="color:var(--fg)">${v}</b></span><span>record ${c.record} · ceiling ${c.ceiling}</span></div>`;
  $("targets").appendChild(d);
});
NOTES.cases.filter(c => c.kind === "calibration").forEach(c => {
  const v = bbc[c.id]?.value || 0, ok = v >= c.record;
  const t = document.createElement("span"); t.className = "tag" + (ok ? " hit" : ""); t.textContent = `${ok ? "✓" : "·"} d${c.d} D${c.D} = ${v}/${c.record}`;
  $("calib").appendChild(t);
});
stat("cost", totalCalls, "Haiku calls");
stat("cost", `${(runs.reduce((s, r) => s + r.out_tokens, 0) / 1e6).toFixed(1)}M`, "output tokens");
stat("cost", runs.reduce((s, r) => s + r.call_errors, 0), "failed calls");
const lim = last.limits || {};
stat("cost", `${Math.round(100 * (lim.seven_day?.utilization ?? 0))}%`, "weekly allowance used (whole account)");
$("costnote").textContent = NOTES.costnote;
</script>
"""


def main():
    out, notes_path, *run_ids = sys.argv[1:]
    data = {r: run_data(r) for r in run_ids}
    notes = json.loads(Path(notes_path).read_text())
    html = TEMPLATE.replace("__DATA__", json.dumps(data)).replace("__NOTES__", json.dumps(notes))
    Path(out).write_text(html)
    print(f"wrote {out} ({len(html)} bytes)")


if __name__ == "__main__":
    main()
