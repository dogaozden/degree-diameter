"""Bipartite version of Delorme's product G * C_m (Grands graphes 1985, sec. 4): G = incidence graph of H(q),
perfect matching M (colour class 0 of the edge colouring) oriented point -> line, other edges line -> point.
Fibre Z_m; along an arc a -> a' the edge (a, x) ~ (a', mu*x). Extra edges parallel to the matching (bipartite stand-in
for the cycle edges of C_m):  variant A: (p,x) ~ (M(p), mu*x + s) for s in OFF;  variant B: (p,x) ~ (M(p), mu*(x+s)).
Output affcheck format (edge p l a b means (p,x) ~ (l, a x + b)).
usage: mk_dstar.py q m mu variant "s1,s2" out [colseed]"""
import sys, os, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
from hexlib import load_hex
q, m, mu, var = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
OFF = [int(x) for x in sys.argv[5].split(',')]; out = sys.argv[6]
colseed = int(sys.argv[7]) if len(sys.argv) > 7 else 1
n, lines = load_hex(q)
col = np.load(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'hex', f'col_q{q}_s{colseed}.npy'))
mui = pow(mu, -1, m)
with open(out, 'w') as f:
    f.write(f"{n} {n} {m} aff\n")
    for l in range(n):
        for k in range(q + 1):
            p = int(lines[l, k])
            if col[l, k] == 0:   # matched edge, arc p -> l: (p,x) ~ (l, mu x)
                f.write(f"{p} {l} {mu} 0\n")
                for s in OFF:
                    b = s % m if var == 'A' else (mu * s) % m
                    f.write(f"{p} {l} {mu} {b}\n")
            else:                # arc l -> p: (l,y) ~ (p, mu y), i.e. (p,x) ~ (l, mu^-1 x)
                f.write(f"{p} {l} {mui} 0\n")
