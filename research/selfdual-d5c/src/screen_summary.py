#!/usr/bin/env python3
"""screen_summary.py K LIST [TAG]: coverage of a screening list in logs/K$K/runs.txt (tag _scr by default): per
category (meta, meta x C_n3, aff, psl/sl) the number of groups run and the lowest energy, and the 10 lowest groups."""
import os, sys
K, lst = sys.argv[1], sys.argv[2]; tag = sys.argv[3] if len(sys.argv) > 3 else "scr"
base = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "logs", f"K{K}")
done = {}
for l in open(os.path.join(base, "runs.txt")):
    w = l.split()
    if w[0].endswith("_" + tag):
        done[w[0][: -len(tag) - 1]] = w[w.index("best") + 1]
cats, best = {}, []
for l in open(lst):
    w = l.split(); g = "_".join(w[1:])
    cat = ("meta" if w[-1] == "1" else "meta x C_n3") if w[1] == "meta" else w[1]
    c = cats.setdefault(cat, [0, 0, None])
    c[0] += 1
    if g in done and done[g] != "NA":
        c[1] += 1; b = int(done[g]); c[2] = b if c[2] is None else min(c[2], b); best.append((b, int(w[0]), " ".join(w[1:])))
for k, (tot, d, b) in cats.items():
    print(f"{k:12s} run {d:4d} of {tot:4d}  lowest {b if b is not None else '-'}")
for b, n, g in sorted(best)[:10]:
    print(b, n, g)
