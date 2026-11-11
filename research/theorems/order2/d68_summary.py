#!/usr/bin/env python3
"""Summary of the (6,8) order-2 comparison (runs/d68/*.log, d68_compare.sh): four symmetries x 6 seeds x 150 s.
Usage: d68_summary.py DIR"""
import re, sys, glob, os
d = sys.argv[1] if len(sys.argv) > 1 else "runs/d68"
cfg = {"psl11x24_r11": "PSL(2,11)xZ24, conjugation, z->11z (rho = 1/23.6)",
       "psl11x24_r23": "PSL(2,11)xZ24, conjugation, z->23z (rho = 1/11.8)",
       "sl25_conj": "SL(2,25), conjugation by a trace-0 matrix (rho = 1/24, |Fix| = 24)",
       "sl25_frob": "SL(2,25), Frobenius x->x^5 (rho = 1/120, |Fix| = 120)"}
print(f"{'symmetry':66s} solved  evals to solve (solved seeds)            best of unsolved seeds")
for key, name in cfg.items():
    sol, rest = [], []
    for f in sorted(glob.glob(os.path.join(d, key + "_s*.log"))):
        m = re.search(r"best=(\d+) evals=(\d+) time=([\d.]+)", open(f).read())
        if not m:
            continue
        b, e, t = int(m.group(1)), int(m.group(2)), float(m.group(3))
        (sol if b == 0 else rest).append((e, t, b))
    n = len(sol) + len(rest)
    print(f"{name:66s} {len(sol)}/{n}    {', '.join(f'{e/1e6:.2f}M ({t:.0f} s)' for e, t, b in sorted(sol)):40s}   "
          f"{', '.join(str(b) for e, t, b in rest)} (at {', '.join(f'{e/1e6:.1f}M' for e, t, b in rest)})")
