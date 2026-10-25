# N = <h, sigma>-invariant exact-cover instances: rows = sigma-orbits of valid h-rows (super-rows), columns = h-orbits.
import numpy as np, sys, pickle
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d16D7_r2/c8')
from load import *
from geo import build_PL
from collections import Counter, defaultdict
q, N, L, LP, X = load_hex()
cands = np.load('sigma_cands.npy'); good = np.load('sigma_good.npy')
S = cands[good[0]] % 13
S = S.astype(np.int64)
det = int(round(np.linalg.det(S))) % 13
dinv = pow(det, 11, 13)
adj = np.zeros((3,3), dtype=np.int64)
for i in range(3):
    for j in range(3):
        minor = np.delete(np.delete(S, j, 0), i, 1)
        adj[i, j] = ((-1) ** (i + j)) * (minor[0,0]*minor[1,1] - minor[0,1]*minor[1,0])
Sinv = (adj * dinv) % 13
assert np.array_equal((S @ Sinv) % 13, np.eye(3, dtype=np.int64))
def normalise1(V):
    V = V % 13
    lead = np.argmax(V != 0, axis=1)
    inv = np.array([0] + [pow(a, 11, 13) for a in range(1, 13)], dtype=np.int64)
    s = inv[V[np.arange(len(V)), lead]]
    return (V * s[:, None]) % 13
code = X @ (13 ** np.arange(7)); order = np.argsort(code); sc = code[order]
def sig_points(pts):
    Xp = X[pts]
    Y = np.zeros((len(pts), 7), dtype=np.int64)
    Y[:, 0:3] = (Xp[:, 0:3] @ S.T) % 13
    Y[:, 3] = Xp[:, 3]
    Y[:, 4:7] = (Xp[:, 4:7] @ Sinv) % 13
    Y = normalise1(Y)
    yc = Y @ (13 ** np.arange(7))
    pos = np.searchsorted(sc, yc)
    assert np.all(sc[np.minimum(pos, len(sc)-1)] == yc)
    return order[pos]
keyd = {tuple(sorted(r)): i for i, r in enumerate(LP.tolist())}
def sig_lines(lines):
    img = sig_points(LP[lines].ravel()).reshape(len(lines), 14)
    return np.array([keyd[tuple(sorted(r))] for r in img.tolist()])
hop = np.load('hop.npy'); hol = np.load('hol.npy')
meta = pickle.load(open('hexact_meta.pkl', 'rb'))
orbs_p, orbs_l = meta['orbs_p'], meta['orbs_l']
# sigma on h-orbits via representatives
sp_map = np.array([hop[sig_points(np.array([orbs_p[o][0]]))[0]] for o in range(len(orbs_p))])
sl_map = np.array([hol[sig_lines(np.array([orbs_l[o][0]]))[0]] for o in range(len(orbs_l))])
# check sigma is an involution-free order-3 permutation on orbits
def cyc(perm):
    seen = set(); out = Counter()
    for i in range(len(perm)):
        if i in seen: continue
        c = 0; j = i
        while j not in seen:
            seen.add(j); j = perm[j]; c += 1
        out[c] += 1
    return dict(out)
print('sigma cycle type on point h-orbits', cyc(sp_map))
print('sigma cycle type on line h-orbits', cyc(sl_map))
np.save('sp_map.npy', sp_map); np.save('sl_map.npy', sl_map)
pickle.dump(dict(S=S, Sinv=Sinv), open('sigma_mat.pkl', 'wb'))
