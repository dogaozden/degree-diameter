#!/usr/bin/env python3
"""deep_pick.py K THR [TAG]: from logs/K$K/out/*_TAG.out (default TAG scr) list the (group, record, type) with the
lowest energy per group, for groups whose best <= THR and that have no deep run yet; lines "best group-args rec f"."""
import glob, os, sys
K, thr = sys.argv[1], int(sys.argv[2]); tag = sys.argv[3] if len(sys.argv) > 3 else "scr"
base = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "logs", f"K{K}")
done = set()
if os.path.exists(os.path.join(base, "runs.txt")):
    for l in open(os.path.join(base, "runs.txt")):
        if "_deep" in l.split()[0]:
            done.add(l.split()[0].split("_deep")[0])
rows = []
for f in glob.glob(os.path.join(base, "out", f"*_{tag}.out")):
    g = os.path.basename(f)[: -len(f"_{tag}.out")]
    best = None
    for l in open(f):
        w = l.split()
        if w and w[0] == "TABU":
            b, r, ft = int(w[w.index("best") + 1]), int(w[2]), int(w[5])
            if best is None or b < best[0]:
                best = (b, r, ft)
    if best and best[0] <= thr and g not in done:
        rows.append((best[0], g.replace("_", " "), best[1], best[2]))
for b, g, r, ft in sorted(rows):
    print(b, g, r, ft)
