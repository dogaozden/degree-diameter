"""prep.py: base graph for lift7.c (card c11, squad r1_d8c).

Base = I(H(5)) (points 0..N-1, lines N..2N-1) with the D7 level matchings: point p is joined to phi(p) = N + perm[p],
perm = default_rng(SEED).permutation(N), by two matchings of type 1 and 2 (the Z_5 level voltages). Same phi as
gen.py "lev 5 5 SEED". Hexagon flags are type 0.
Output lines: "V" then "type u v c" (type 0 = hex flag, c = 0; type 1 = matching, c = 1 or 2).
Usage: python3 prep.py SEED OUT
"""
import sys
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d10D8_work')
from hexlib import load

seed, out = int(sys.argv[1]), sys.argv[2]
N, LP, PL, coord = load(5)
rng = np.random.default_rng(seed)
phi = rng.permutation(N) + N
rows = []
for l in range(LP.shape[0]):
    for p in LP[l]:
        rows.append((0, int(p), N + l, 0))
for p in range(N):
    rows.append((1, p, int(phi[p]), 1))
    rows.append((1, p, int(phi[p]), 2))
with open(out, 'w') as f:
    f.write(f'{2 * N}\n')
    for r in rows:
        f.write('%d %d %d %d\n' % r)
print('V', 2 * N, 'edges', len(rows))
