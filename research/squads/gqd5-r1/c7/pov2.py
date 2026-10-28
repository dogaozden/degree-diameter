"""tabu search for independent sets of size K in W(5) (mode 'W') or Q(4,5) (mode 'Q'), avoiding a forbidden list (card c7).
usage: pov2.py MODE K SEED SECS [forbid.json]"""
import sys, json, time
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
from gqlib import W, Q4

mode, K, seed, secs = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4])
forbid = json.load(open(sys.argv[5])) if len(sys.argv) > 5 else []
G = W(5) if mode == 'W' else Q4(5)
N = G.np
allowed = np.ones(N, dtype=bool)
allowed[forbid] = False
A = G.col.astype(np.int32)
A[:, ~allowed] = 0
A[~allowed, :] = 0
rng = np.random.default_rng(seed)
cand = np.nonzero(allowed)[0]
t0 = time.time()
res = None
while res is None and time.time() - t0 < secs:
    inS = np.zeros(N, dtype=bool)
    inS[rng.choice(cand, K, replace=False)] = True
    tu = np.zeros(N, dtype=np.int64)
    it = 0
    restart = time.time()
    while time.time() - restart < 25:
        it += 1
        cnt = A @ inS
        cost = int(cnt[inS].sum() // 2)
        if cost == 0:
            res = sorted(np.nonzero(inS)[0].tolist())
            break
        ins = np.nonzero(inS)[0]
        outs = cand[~inS[cand]]
        conf_in = ins[cnt[ins] > 0]
        dd = cnt[outs][None, :] - A[np.ix_(conf_in, outs)] - cnt[conf_in][:, None]
        mask = tu[outs][None, :] > it
        dd = np.where(mask & (dd + cost >= cost), 10**6, dd)
        m = dd.min()
        idx = np.argwhere(dd == m)
        i, j = idx[rng.integers(len(idx))]
        v = conf_in[i]
        u = outs[j]
        inS[v] = False
        inS[u] = True
        tu[v] = it + 10 + rng.integers(10)
        tu[u] = it + 3 + rng.integers(4)
print(mode, 'K', K, 'found' if res else 'none', res, flush=True)
if res:
    out = '/home/user/degree-diameter/research/squads/gqd5-r1/c7/%s%d_s%d.json' % (mode, K, seed)
    json.dump(res, open(out, 'w'))
