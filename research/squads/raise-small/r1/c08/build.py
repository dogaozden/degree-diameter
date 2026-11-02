#!/usr/bin/env python3
"""build.py TAB SOL OUT.edges: lift edge list from a salift_s solution over the group table TAB (gen.py format).
Lift: vertex (u,g) = u*N+g; base edge (u,v,x) gives (u,g) ~ (v, g*x) for all g. Header of SOL: "N id p [cost]".
Checks the table (identity, associativity on random triples) and that the lift is simple and cubic."""
import sys
import numpy as np
tab, sol, out = sys.argv[1], sys.argv[2], sys.argv[3]
tok = open(tab).read().split()
N = int(tok[1]); T = np.array(tok[4:4 + N * N], dtype=np.int64).reshape(N, N)
ar = np.arange(N)
assert (T[0] == ar).all() and (T[:, 0] == ar).all()
rng = np.random.default_rng(2); a, b, c = rng.integers(0, N, (3, 200000))
assert (T[T[a, b], c] == T[a, T[b, c]]).all(), 'not associative'
lines = [l.split() for l in open(sol) if l.strip()]
hN, hid, p = int(lines[0][0]), lines[0][1], int(lines[0][2])
assert hN == N, (hN, N)
base = [tuple(map(int, t[:3])) for t in lines[1:]]
nb = 2 * p
E = set()
for (u, v, x) in base:
    for g in range(N):
        s, t = u * N + g, v * N + int(T[g, x])
        E.add((min(s, t), max(s, t)))
n = nb * N
deg = np.zeros(n, dtype=int)
for s, t in E:
    deg[s] += 1; deg[t] += 1
assert (deg == 3).all() and len(E) == 3 * n // 2 and all(s != t for s, t in E), 'not simple cubic'
with open(out, 'w') as f:
    f.write(f"{n}\n")
    for s, t in sorted(E):
        f.write(f"{s} {t}\n")
print('n =', n, 'edges =', len(E), 'written', out)
