import numpy as np, sys, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d16D7_r2/c8')
from load import *
q, N, L, LP, X = load_hex()
cands = np.load('sigma_cands.npy')
inv_t = None
def normalise(V):
    V = V % 13
    lead = np.argmax(V != 0, axis=1)
    inv = np.array([0] + [pow(a, 11, 13) for a in range(1, 13)], dtype=np.int64)
    s = inv[V[np.arange(len(V)), lead]]
    return (V * s[:, None]) % 13
code = X @ (13 ** np.arange(7))
order = np.argsort(code); sc = code[order]
def perm_of(S, pts):
    Si = np.round(np.linalg.inv(S.astype(float)) * 1).astype(np.int64)
    # exact inverse mod 13
    from itertools import product
    Sinv = None
    # compute inverse mod 13 by adjugate
    det = int(round(np.linalg.det(S))) % 13
    dinv = pow(det, 11, 13)
    adj = np.zeros((3,3), dtype=np.int64)
    for i in range(3):
        for j in range(3):
            minor = np.delete(np.delete(S, j, 0), i, 1)
            adj[i, j] = ((-1) ** (i + j)) * (minor[0,0]*minor[1,1] - minor[0,1]*minor[1,0])
    Sinv = (adj * dinv) % 13
    Y = np.zeros((len(pts), 7), dtype=np.int64)
    Xp = X[pts]
    Y[:, 0:3] = (Xp[:, 0:3] @ S.T) % 13
    Y[:, 3] = Xp[:, 3]
    Y[:, 4:7] = (Xp[:, 4:7] @ Sinv) % 13      # w' = S^{-T} w  (row form: w^T S^{-1})
    Y = normalise(Y)
    yc = Y @ (13 ** np.arange(7))
    pos = np.searchsorted(sc, yc)
    assert np.all(sc[np.minimum(pos, len(sc)-1)] == yc), 'image not on quadric'
    return order[pos]
# line key dictionary
keys = set(tuple(sorted(r)) for r in LP.tolist())
rng = np.random.default_rng(5)
samp = rng.choice(L, 1500, replace=False)
good = []
t0 = time.time()
for ci, S in enumerate(cands):
    ok = True
    pts = LP[samp].ravel()
    img = perm_of(S, pts).reshape(len(samp), 14)
    for r in img:
        if tuple(sorted(r.tolist())) not in keys:
            ok = False; break
    if ok: good.append(ci)
print('candidates', len(cands), 'H-collineations among sampled lines:', len(good), 'time', round(time.time()-t0,1))
np.save('sigma_good.npy', np.array(good))
