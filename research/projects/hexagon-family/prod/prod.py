"""Product candidates in Q(6,q), q odd prime: V7 = E4 (elliptic, Q^-(3,q)) + C3 (conic), orthogonal.
Candidates: (x, lam*y), x elliptic-quadric point, y conic point, lam in F_q^*, plus (x,0), (0,y).
Writes the conflict graph (B = 0) for mis.c and the candidate vectors (in our coordinates via to_std).
usage: python3 prod.py q OUTPREFIX"""
import sys, numpy as np
sys.path.insert(0, '../tools'); from q6lib import Geo, inv_mod
q = int(sys.argv[1]); pre = sys.argv[2]; G = Geo(q)
# nonsquare
ns = next(a for a in range(2, q) if pow(a, (q - 1) // 2, q) == q - 1)
# abstract basis: E4 with form x0x1 - (z0^2 - ns z1^2) (elliptic), C3 with form y0y2 - y1^2 (conic)
Gram = np.zeros((7, 7), dtype=np.int64)
Gram[0, 1] = Gram[1, 0] = 1; Gram[2, 2] = -2; Gram[3, 3] = 2 * ns       # polar of x0x1 - z0^2 + ns z1^2
Gram[4, 6] = Gram[6, 4] = 1; Gram[5, 5] = -2                           # polar of y0y2 - y1^2
Gram %= q
def Q(v): return int((v @ Gram @ v) * pow(2, q - 2, q)) % q
E = []
for z0 in range(q):
    for z1 in range(q):
        Nz = (z0 * z0 - ns * z1 * z1) % q
        E.append(np.array([1, Nz, z0, z1, 0, 0, 0]))
E.append(np.array([0, 1, 0, 0, 0, 0, 0]))
C = [np.array([0, 0, 0, 0, 1, t, t * t % q]) for t in range(q)] + [np.array([0, 0, 0, 0, 0, 0, 1])]
cand = [x for x in E] + [y for y in C]
for x in E:
    for y in C:
        for lam in range(1, q):
            cand.append((x + lam * y) % q)
cand = np.array(cand, dtype=np.int64)
assert all(Q(v) == 0 for v in cand)
Bm = (cand @ Gram @ cand.T) % q
n = len(cand); iu = np.triu_indices(n, 1); conf = Bm[iu] == 0
eu, ev = iu[0][conf], iu[1][conf]
with open(pre + '.graph', 'w') as f:
    f.write('%d %d\n' % (n, len(eu)))
    for a, b in zip(eu, ev): f.write('%d %d\n' % (a, b))
T = G.to_std(Gram)
ids = G.ids_of((cand @ T.T) % q)
np.save(pre + '_ids.npy', ids)
print('q', q, 'candidates', n, 'conflicts', len(eu))
