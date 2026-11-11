# Build H-orbit candidates (H = Aut(G), order 66) from the r2/d06 candidate covers, then greedy H-orbit packing per side.
import numpy as np, sys, glob, time, pickle
sys.path.insert(0,'/home/user/degree-diameter/research/squads/beyond-small/r3/e07')
from h66 import PERMS, H
PL = np.stack([PERMS[k] for k in sorted(PERMS)])        # 66 x H
E = np.loadtxt('/home/user/degree-diameter/research/squads/beyond-small/data/d16D5_n33792.edges', skiprows=1, dtype=np.int64)
a = E[:,0]; b = E[:,1]-H
adjA = np.zeros((H,16), dtype=np.int64); adjB = np.zeros((H,16), dtype=np.int64)
ca = np.zeros(H, dtype=np.int64); cb = np.zeros(H, dtype=np.int64)
for x, y in zip(a, b):
    adjA[x, ca[x]] = y; ca[x] += 1
    adjB[y, cb[y]] = x; cb[y] += 1
assert (ca == 16).all() and (cb == 16).all()
def D2set(Nloc, side):
    """side = 'A' hubs (N subset of B): T=B. returns local T-indices of N and of ball2(N) minus N."""
    if side == 'A':   # T = B, S = A
        S = np.unique(adjB[Nloc].ravel()); T2 = np.unique(adjA[S].ravel()); adjT = adjA
    else:             # T = A, S = B
        S = np.unique(adjA[Nloc].ravel()); T2 = np.unique(adjB[S].ravel()); adjT = adjB
    return np.setdiff1d(T2, Nloc)
def load_cands():
    cands = {'A': [], 'B': []}   # 'A': hubs on side A, i.e. N subset of B (ids >= H)
    for p in sorted(glob.glob('/home/user/degree-diameter/research/squads/beyond-small/r2/d06/cand_*.txt')):
        for line in open(p):
            ids = line.split()
            if not ids: continue
            ids = np.array([int(x) for x in ids])
            if ids[0] >= H: cands['A'].append(ids - H)
            else: cands['B'].append(ids)
    return cands
def build_orbits(side, cl):
    seen = {}
    for loc in cl:
        imgs = np.sort(PL[:, loc], axis=1)                  # 66 x k
        key = min(map(tuple, imgs))
        if key in seen: continue
        seen[key] = np.array(key, dtype=np.int64)
    out = []
    for key, base in seen.items():
        k = len(base)
        dist = set(map(tuple, np.sort(PL[:, base], axis=1)))
        allv = np.concatenate([np.array(d) for d in dist])
        if len(np.unique(allv)) != len(allv):   # images overlap -> invalid orbit
            continue
        D2 = D2set(base, side)
        m = np.zeros(H, bool); m[D2] = True
        # self compat: every other image must hit D2
        ok = True
        for d in dist:
            if d == key: continue
            if not m[np.array(d)].any(): ok = False; break
        if not ok: continue
        out.append((base, len(dist)))
    return out
if __name__ == '__main__':
    t0 = time.time()
    cands = load_cands()
    res = {}
    for side in 'AB':
        orbs = build_orbits(side, cands[side])
        res[side] = orbs
        print('side', side, 'cands', len(cands[side]), 'valid H-orbits', len(orbs),
              'orbit sizes (distinct hubs)', np.bincount([s for _, s in orbs]).nonzero()[0].tolist(), time.time()-t0, flush=True)
    pickle.dump(res, open('/home/user/degree-diameter/research/squads/beyond-small/r3/e07/horbs.pkl', 'wb'))
