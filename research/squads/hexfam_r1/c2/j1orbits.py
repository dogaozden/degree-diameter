import sys, numpy as np, time, pickle
sys.path.insert(0, '/home/user/degree-diameter/research/projects/hexagon-family/tools')
sys.path.insert(0, '/home/user/degree-diameter/research/squads/hexfam_r1/c2')
from q6lib import Geo, orbits, inv_mod, A7
from j1setup import Y, Z, q
G = Geo(q)
t0 = time.time()
X = np.eye(7, dtype=np.int64)
T = G.to_std(X)
Ti = inv_mod(T, q)
def conj(g):
    return (T @ g @ Ti) % q
# sanity: M preserves A7
for g in [Y, Z]:
    M = conj(g)
    assert ((M.T @ A7 @ M - A7) % q == 0).all(), 'not isometry of A7'
PY = G.perm(conj(Y)); PZ = G.perm(conj(Z))
print('perms built', time.time() - t0, flush=True)
# sanity: perm preserves opposition on a random sample
rng = np.random.default_rng(0)
s = rng.integers(0, G.N, 200)
Bs = G.B(G.C[s], G.C[s]) != 0
Bp = G.B(G.C[PY[s]], G.C[PY[s]]) != 0
print('Y preserves opp on sample', (Bs == Bp).all(), flush=True)
lab = orbits(G.N, [PY, PZ])
np.save('/home/user/degree-diameter/research/squads/hexfam_r1/c2/j1_orbit_lab.npy', lab)
np.save('/home/user/degree-diameter/research/squads/hexfam_r1/c2/PY.npy', PY)
np.save('/home/user/degree-diameter/research/squads/hexfam_r1/c2/PZ.npy', PZ)
cnt = np.bincount(lab)
print('num J1 orbits', len(cnt), 'sizes', sorted(cnt.tolist()), time.time() - t0)
