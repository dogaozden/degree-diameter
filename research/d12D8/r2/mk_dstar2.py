"""Bipartite version of Delorme's G * C_m, take 2. G = incidence graph of H(q); perfect matching M0 = colour class 0,
oriented point -> line, all other edges line -> point; along an arc a -> a': (a,x) ~ (a', mu x).
Cycle edges cross sides through a partner bijection P: (p,x) ~ (P(p), x + s) for s in OFF (default +1,-1).
partner: match (P = M0, cycle edges parallel to the matched arcs) | rand (random bijection) | match1 (colour class 1).
usage: mk_dstar2.py q m mu partner "s1,s2" out [colseed] [seed]"""
import sys, os, random, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
from hexlib import load_hex
q, m, mu, partner = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
OFF = [int(x) for x in sys.argv[5].split(',')]; out = sys.argv[6]
colseed = int(sys.argv[7]) if len(sys.argv) > 7 else 1
random.seed(int(sys.argv[8]) if len(sys.argv) > 8 else 1)
n, lines = load_hex(q)
col = np.load(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'hex', f'col_q{q}_s{colseed}.npy'))
mui = pow(mu, -1, m)
def cls(c):
    M = [-1] * n
    for l in range(n):
        for k in range(q + 1):
            if col[l, k] == c: M[int(lines[l, k])] = l
    return M
if partner == 'match': P = cls(0)
elif partner == 'match1': P = cls(1)
else: P = list(range(n)); random.shuffle(P)
with open(out, 'w') as f:
    f.write(f"{n} {n} {m} aff\n")
    for l in range(n):
        for k in range(q + 1):
            p = int(lines[l, k])
            if col[l, k] == 0: f.write(f"{p} {l} {mu} 0\n")
            else: f.write(f"{p} {l} {mui} 0\n")
    for p in range(n):
        for s in OFF: f.write(f"{p} {P[p]} 1 {s % m}\n")
