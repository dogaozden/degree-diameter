"""gen_dual.py (card c5): Z_m lift of I(H(q)) + two duality matchings.
Usage: python3 -I gen_dual.py q phifile m W_seed OUT [rule]
Base graph: points 0..N-1, lines N..2N-1 of H(q).  phi = duality (2N ints).
Extra edges: for each point p the matching edge (p, phi(p)) with voltage a(p), and for each line l the edge
(phi(l), l) with voltage b(l).  Hexagon flags (p,l) get voltage h(p,l).
Rule 'bil' (default): with c(x) the 7 coordinates of x (dual coordinates c(phi(l)) for lines),
  a(p) = c(p).u,  b(l) = c(phi(l)).v,  h(p,l) = c(p).W.c(phi(l)),  all mod m; weights u,v,W drawn from seed.
Rule 'zero': hexagon voltages 0, a = 1, b = 2 (baseline). Rule 'lem': as zero with a = 1, b = 4 (the Z_10 lemma).
"""
import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d10D8_work')
from hexlib import load
q, phif, m, seed, out = int(sys.argv[1]), sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
rule = sys.argv[6] if len(sys.argv) > 6 else 'bil'
N, LP, PL, coord = load(q)
phi = np.fromfile(phif, dtype=np.int32).astype(np.int64)
assert phi.shape[0] == 2 * N
rng = np.random.default_rng(seed)
C = coord.astype(np.int64)                 # (N,7) point coordinates
dualC = C[phi[N:]]                          # for line l (index N+l): coords of its dual point phi(l)  (phi(l) < N)
rows = []
L, Q1 = LP.shape
u = rng.integers(0, m, 7); v = rng.integers(0, m, 7); W = rng.integers(0, m, (7, 7))
if rule in ('zero', 'lem'):
    A, B = (1, 4) if rule == 'lem' else (1, 2)
    for l in range(L):
        for p in LP[l]:
            rows.append((p, N + l, 0))
    for p in range(N):
        rows.append((p, phi[p], A % m))
    for l in range(L):
        rows.append((phi[N + l], N + l, B % m))
else:
    for l in range(L):
        for p in LP[l]:
            h = int(C[p] @ W @ dualC[l]) % m
            rows.append((int(p), N + l, h))
    for p in range(N):
        rows.append((p, int(phi[p]), int(C[p] @ u) % m))
    for l in range(L):
        rows.append((int(phi[N + l]), N + l, int(dualC[l] @ v) % m))
with open(out, 'w') as f:
    f.write(f'Z {m}\n{2*N}\n')
    f.write(' '.join(['0'] * N + ['1'] * N) + '\n')
    for r in rows:
        f.write('%d %d %d\n' % r)
