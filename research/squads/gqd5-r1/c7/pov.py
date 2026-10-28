"""fixed-size tabu search for a partial ovoid (independent set) of size K in W(5) (card c7).
State: K points; cost = number of collinear pairs inside; swap moves chosen by min delta with tabu."""
import sys, random, json, time
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
from gqlib import W
Wg = W(5); N = Wg.np
A = Wg.col.astype(np.int32)

def tabu(K, seed, secs, init=None):
    rng = np.random.default_rng(seed)
    inS = np.zeros(N, dtype=bool)
    S0 = rng.choice(N, K, replace=False) if init is None else np.array(init)
    inS[S0] = True
    tabu_until = np.zeros(N, dtype=np.int64)
    t0 = time.time(); it = 0
    while True:
        it += 1
        cnt = A @ inS                    # neighbours in S for every vertex
        cost = int(cnt[inS].sum() // 2)
        if cost == 0:
            return sorted(np.nonzero(inS)[0].tolist())
        if time.time() - t0 > secs:
            return None
        ins = np.nonzero(inS)[0]; outs = np.nonzero(~inS)[0]
        # delta of removing v (in S) and adding u (out): (cnt[u] - A[u,v]) - (cnt[v])  [cnt[v] counts its S-neighbours]
        conf_in = ins[cnt[ins] > 0]      # only vertices in conflict are worth removing
        if len(conf_in) == 0: conf_in = ins
        dd = cnt[outs][None, :] - A[np.ix_(conf_in, outs)] - cnt[conf_in][:, None]
        mask = tabu_until[outs][None, :] > it
        # aspiration: allow tabu if it gives new best (cost-delta < 0 minimal) -- simple version
        dd = np.where(mask & ~(dd + cost < cost), 10**6, dd)
        m = dd.min()
        idx = np.argwhere(dd == m)
        i, j = idx[rng.integers(len(idx))]
        v = conf_in[i]; u = outs[j]
        inS[v] = False; inS[u] = True
        tabu_until[v] = it + 10 + rng.integers(10)
        tabu_until[u] = it + 3 + rng.integers(4)

if __name__ == '__main__':
    K = int(sys.argv[1]); seed = int(sys.argv[2]); secs = float(sys.argv[3])
    res = None; s = seed
    t0 = time.time()
    while res is None and time.time() - t0 < secs:
        res = tabu(K, s, 20); s += 1000
    print('K', K, 'found' if res else 'none', res, 'tries', (s - seed) // 1000)
    if res:
        json.dump(res, open('/home/user/degree-diameter/research/squads/gqd5-r1/c7/P%d_%d.json' % (K, seed), 'w'))
