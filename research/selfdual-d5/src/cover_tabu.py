#!/usr/bin/env python3
"""cover_tabu.py: per-order summary of tabu sweeps (logs/K9/tabu.txt, logs/K9/meta.txt): groups run, best energy
(smallest |G \\ X X| reached), groups with solutions.  Tabu runs are heuristic, not exhaustive.
usage: cover_tabu.py LOG [LOG ...]"""
import sys, collections
by = collections.defaultdict(lambda: [0, None, []])
for p in sys.argv[1:]:
    for l in open(p):
        t = l.split()
        if len(t) < 4 or not t[0].isdigit() or "GAPFAIL" in t: continue
        d = dict(zip(t[2::2], t[3::2])); n = int(t[0])
        if d.get("rc") != "0": continue
        b = int(d["best"]) if d.get("best", "NA") != "NA" else None
        e = by[n]; e[0] += 1
        if b is not None and (e[1] is None or b < e[1]): e[1] = b
        if int(d.get("sols", 0)): e[2].append(t[1])
print("| order | vertices | groups run | best \\|G \\ XX\\| | groups with solutions |")
print("|---:|---:|---:|---:|---|")
for n in sorted(by):
    g, b, h = by[n]
    print(f"| {n} | {2 * n} | {g} | {b if b is not None else '-'} | {', '.join(h) or '-'} |")
