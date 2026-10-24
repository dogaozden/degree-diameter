#!/usr/bin/env python3
"""Summary for card c4: E18 per variant from results.jsonl.

Only runs that finished on their own count: rc 0 (solved) or rc 1 (budget reached, unsolved).
rc 124 (killed by the hard timeout before the budget) and runs without a RESULT line are listed but not scored.
E18 = median(adj evals) * exp((18 - mu)/4.5), adj = evals if solved else 3 * evals.
"""
import json, math, os, statistics
HERE = os.path.dirname(os.path.abspath(__file__))
recs = [json.loads(l) for l in open(os.path.join(HERE, "results.jsonl")) if l.strip()]
ORDER = ["default", "K4", "K16", "TARGP40", "TARGP95", "TMAX0.8_TMIN0.08", "TMAX3_TMIN0.3",
         "RESTART1_REHEAT20_RSTEPS100", "VCLOCK0.01_COOL2"]
mu = next(r["mu"] for r in recs if r.get("mu"))
stats = {}
for name in ORDER:
    rs = sorted([r for r in recs if r["variant"] == name], key=lambda r: r["seed"])
    ok = [r for r in rs if r.get("rc") in (0, 1) and "adj_evals" in r]
    stats[name] = (rs, ok)
e18 = {}
for name, (rs, ok) in stats.items():
    if ok:
        e18[name] = statistics.median([r["adj_evals"] for r in ok]) * math.exp((18 - mu) / 4.5)
base = e18.get("default")
lines = [f"mu={mu}; E18 = median(adj evals) * exp((18-mu)/4.5); scored = runs with rc 0 or 1",
         f"{'variant':29s} K  scored  solved  per-seed evals/best              median     E18  E18/def  ms/eval"]
for name in ORDER:
    rs, ok = stats[name]
    if not rs:
        lines.append(f"{name:29s} (not run)")
        continue
    K = rs[0]["K"]
    if not ok:
        lines.append(f"{name:29s} {K:2d}  0/{len(rs)}   -        not scored: {len(rs)} run(s) killed at hard timeout or no RESULT")
        continue
    med = statistics.median([r["adj_evals"] for r in ok])
    per = " ".join(f"s{r['seed']}:{r['evals']}/{r['best']}" for r in ok)
    ms = statistics.mean(1000 * r["time"] / r["evals"] for r in ok)
    ratio = f"{e18[name] / base:6.2f}" if base else "   n/a"
    lines.append(f"{name:29s} {K:2d}  {len(ok)}/{len(rs)}    {sum(r['solved'] for r in ok)}/{len(ok)}    {per:28s} {med:8.0f} {e18[name]:7.0f} {ratio}  {ms:7.1f}")
best = min(e18, key=e18.get) if e18 else None
lines.append(f"best by E18: {best} = {e18[best]:.0f}; default = {base:.0f}" if base else "no default scored")
text = "\n".join(lines)
open(os.path.join(HERE, "summary.txt"), "w").write(text + "\n")
print(text)
