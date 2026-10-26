"""mk2.py: q=4 lift with Artin-Schreier (trace) structured hexagon voltages (c16).
usage: python3 mk2.py m seed j mode out
  GF(4) encoding: 0,1,2=w,3=w^2 ; Tr(x) = x>>1 (Tr(0)=Tr(1)=0, Tr(w)=Tr(w^2)=1).
  mode 'pos': hex voltage on flag (p,l) = (m/2) * Tr(c_j(p)) * pos(p,l) mod 2, pos = index of p on l
  mode 'lin': hex voltage on flag = (m/2)*Tr(c_j(p)+c_k(p)) for a random pair (j,k) mixed with random 0/1 bit per line
  mode 'rnd': random Z_m hex voltages (control)
Matchings: random bijections points->lines avoiding incidences, random voltages in Z_m.
"""
import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d10D8_work')
from hexlib import load
m, seed, j, mode, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], sys.argv[5]
rng = np.random.default_rng(seed)
q = 4
N, LP, PL, coord = load(q)
C = coord.astype(int)
def tr(x): return (x >> 1) & 1
inc = {(int(p), l) for l in range(N) for p in LP[l]}
edges = []
ks = rng.integers(0, 7, size=2)
for l in range(N):
    for k, p in enumerate(LP[l]):
        p = int(p)
        if mode == 'pos':
            v = (m // 2) * (tr(C[p, j]) * (k & 1)) % m
        elif mode == 'lin':
            v = (m // 2) * ((tr(C[p, j]) + tr(C[p, ks[0]]) + tr(C[p, ks[1]]) + l) % 2) % m
        else:
            v = int(rng.integers(m))
        edges.append((p, l, v))
for t in range(2):
    while True:
        perm = rng.permutation(N)
        if all((p, int(perm[p])) not in inc for p in range(N)):
            break
    for p in range(N):
        edges.append((p, int(perm[p]), int(rng.integers(m))))
seen = set()
for e in edges:
    if e in seen:  # resample matching voltage instead of duplicating
        pass
    seen.add(e)
assert len(seen) == len(edges)
with open(out, 'w') as f:
    f.write(f'{N} {N} {m}\n')
    for a, b, v in edges:
        f.write(f'{a} {b} {v}\n')
print(out)
