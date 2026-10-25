"""Non-bipartite Delorme product G * C_m (Grands graphes 1985, sec. 4) for G = incidence graph of H(q) (vertices: points
0..n-1, lines n..2n-1). Orientation: matching (colour 0) point -> line, others line -> point. Arc a -> a': (a,x)~(a',mu x).
Cycle edges (a,x) ~ (a, x+1). usage: mk_gstar.py q m mu out"""
import sys, os, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
from hexlib import load_hex
q, m, mu, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
n, lines = load_hex(q)
col = np.load(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'hex', f'col_q{q}_s1.npy'))
with open(out, 'w') as f:
    f.write(f"{2*n} {m}\n")
    for l in range(n):
        for k in range(q + 1):
            p = int(lines[l, k])
            if col[l, k] == 0: f.write(f"{p} {n+l} {mu} 0\n")
            else: f.write(f"{n+l} {p} {mu} 0\n")
    for a in range(2 * n): f.write(f"{a} {a} 1 1\n")
