"""mk.py: write lifteval base graphs for H(q) with two matchings (c16 card).
usage: python3 mk.py q m seed hexmode out   (hexmode: zero | rand)
Base: side A = points 0..N-1, side B = lines 0..N-1. Incidences (p,l) voltage v_hex.
Matchings: sigma_t bijection points->lines (random, avoiding incidences), voltages random in Z_m.
"""
import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d10D8_work')
from hexlib import load
q, m, seed, hexmode, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], sys.argv[5]
rng = np.random.default_rng(seed)
N, LP, PL, coord = load(q)
inc = set()
for l in range(N):
    for p in LP[l]:
        inc.add((int(p), l))
edges = []
for l in range(N):
    for p in LP[l]:
        v = 0 if hexmode == 'zero' else int(rng.integers(m))
        edges.append((int(p), l, v))
for t in range(2):
    while True:
        perm = rng.permutation(N)
        if all((p, int(perm[p])) not in inc for p in range(N)):
            break
    # avoid duplicate (p,l) with equal voltage between matchings: just check pairs unique
    for p in range(N):
        edges.append((p, int(perm[p]), int(rng.integers(m))))
# check no duplicate (a,b) pairs with same voltage
seen = set()
for a, b, v in edges:
    assert (a, b, v) not in seen
    seen.add((a, b, v))
with open(out, 'w') as f:
    f.write(f'{N} {N} {m}\n')
    for a, b, v in edges:
        f.write(f'{a} {b} {v}\n')
print(out, len(edges))
