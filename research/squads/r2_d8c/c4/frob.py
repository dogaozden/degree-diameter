"""frob.py (card c4): Frobenius x -> x^3 on GF(9) coordinates, tested as a collineation of H(9) (points -> points,
lines -> lines). Writes frob9.npy (point permutation F on 0..N-1) if it is a collineation."""
import sys
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d10D8_work')
sys.path.insert(0, '/home/user/degree-diameter/research/squads/r2_d8c/c4')
from hexlib import load
from gen_c4 import gf_tables
q = 9
N, LP, PL, coord = load(q)
ADD, MUL, NEG, INV = gf_tables(q)
cube = [MUL[x][MUL[x][x]] for x in range(q)]
C = coord.astype(np.int64)
idx = {tuple(r): i for i, r in enumerate(C.tolist())}
F = np.empty(N, dtype=np.int64)
for i in range(N):
    img = tuple(cube[v] for v in C[i].tolist())
    F[i] = idx[img]
lset = {frozenset(LP[l].tolist() if hasattr(LP[l], 'tolist') else LP[l]): l for l in range(N)}
ok = 0
for l in range(N):
    S = frozenset(int(F[p]) for p in LP[l])
    if S in lset:
        ok += 1
print('lines mapped to lines:', ok, 'of', N, '; points bijective:', len(set(F.tolist())) == N)
if ok == N:
    np.save('/home/user/degree-diameter/research/squads/r2_d8c/c4/frob9.npy', F)
