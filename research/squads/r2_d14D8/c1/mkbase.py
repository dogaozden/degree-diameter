"""mkbase.py design k out: expand a quotient design (qsa format) to the full base graph for lifteval (c1).
Point (a, i) = g^a repP[i], line (b, K) = g^b repL[K]; slot (i, s) = (K, T, LEV, C) gives the edges
(g^a repP[i], g^(a+T) repL[K]) with voltage (LEV + 5C) mod 5k, for every a in Z_S."""
import sys
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d14D8_work')
from hexlib import write_base, HERE
design, k, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
z = np.load(HERE / 'hex' / f'sym_q{sys.argv[4]}.npz')
S = int(z['S']); gperm = z['gperm']; glperm = z['glperm']; repP = z['repP']; repL = z['repL']
N = len(gperm); NP = len(repP)
with open(design) as f:
    NP2, S2, D = map(int, f.readline().split())
    assert (NP2, S2) == (NP, S)
    slots = np.array([list(map(int, ln.split())) for ln in f if ln.strip()], dtype=np.int64)
assert len(slots) == NP * D
m = 5 * k
PT = np.zeros((S, NP), dtype=np.int64); LT = np.zeros((S, NP), dtype=np.int64)
PT[0] = repP; LT[0] = repL
for a in range(1, S):
    PT[a] = gperm[PT[a - 1]]; LT[a] = glperm[LT[a - 1]]
E = []
for i in range(NP):
    for s in range(D):
        K, T, lev, c = slots[D * i + s]
        w = (lev + 5 * c) % m
        for a in range(S):
            E.append((PT[a, i], LT[(a + T) % S, K], w))
E = np.array(E, dtype=np.int64)
deg_p = np.bincount(E[:, 0], minlength=N); deg_l = np.bincount(E[:, 1], minlength=N)
assert (deg_p == D).all() and (deg_l == D).all(), (deg_p.min(), deg_p.max(), deg_l.min(), deg_l.max())
write_base(out, N, m, E)
print(f'wrote {out}: N={N} m={m} edges={len(E)} degree={D}')
