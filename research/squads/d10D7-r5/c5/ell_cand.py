# c5: candidate list = points of Q(6,8) on the elliptic hyperplane section X3 = L(v) (L linear, Q_L elliptic, 4617 points).
# Writes ell_cand_ids.txt (hex_q8 point ids). Run: python3 ell_cand.py
import numpy as np, sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D7-r5/c5')
from torus8 import P6, MUL, load_hex8, normalize_rows
q, N, X8 = load_hex8()
allv = P6
def Lval(c, V):
    acc = np.zeros(V.shape[0], dtype=np.int64)
    for i in range(6): acc ^= MUL[c[i], V[:, i]]
    return acc
rng = np.random.default_rng(3)
found = []
for trial in range(400):
    c = rng.integers(0, 8, size=6)
    Lv = Lval(c, allv)
    Qv = MUL[allv[:,0], allv[:,3]] ^ MUL[allv[:,1], allv[:,4]] ^ MUL[allv[:,2], allv[:,5]] ^ MUL[Lv, Lv]
    if int((Qv == 0).sum()) == 4617:
        found.append(c.copy()); break
c = found[0]
Lv = Lval(c, allv)
Qv = MUL[allv[:,0], allv[:,3]] ^ MUL[allv[:,1], allv[:,4]] ^ MUL[allv[:,2], allv[:,5]] ^ MUL[Lv, Lv]
Z = allv[Qv == 0]; LZ = Lv[Qv == 0]
X7 = np.stack([Z[:,0], Z[:,1], Z[:,2], LZ, Z[:,3], Z[:,4], Z[:,5]], axis=1)
X7n = normalize_rows(X7)
idx7 = np.full(8**7, -1, dtype=np.int64); idx7[X8 @ (8 ** np.arange(7))] = np.arange(N)
ids = idx7[X7n @ (8 ** np.arange(7))]
assert (ids >= 0).all()
np.savetxt(sys.argv[1] if len(sys.argv) > 1 else 'ell_cand_ids.txt', ids, fmt='%d')
print('L =', c.tolist(), 'candidates', len(ids))
