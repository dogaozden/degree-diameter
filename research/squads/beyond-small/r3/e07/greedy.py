import numpy as np, pickle, sys, time
sys.path.insert(0,'/home/user/degree-diameter/research/squads/beyond-small/r3/e07')
from h66 import PERMS, H
PL = np.stack([PERMS[k] for k in sorted(PERMS)])
sys.path.insert(0,'.')
from hpack import D2set
def prep(side, orbs):
    n = len(orbs)
    Rall = np.full((n, 66, 17), H, dtype=np.int64)
    MN = np.zeros((n, H+1), bool); MD = np.zeros((n, H+1), bool)
    for p,(base,_) in enumerate(orbs):
        k = len(base)
        Rall[p,:,:k] = PL[:, base]
        MN[p, base] = True
        MD[p, D2set(base, side)] = True
    return Rall, MN, MD
def compat_row(o, pool, Rall, MN, MD):
    R = Rall[pool]                                  # |pool| x 66 x 17
    hitN = MN[o][R].any(axis=2)                     # images of pool hitting N_o
    hitD = MD[o][R].any(axis=2)                     # images of pool hitting D2(N_o)
    return (~hitN).all(axis=1) & hitD.all(axis=1)
def greedy(pool0, Rall, MN, MD, rng, pick='random'):
    pool = np.array(pool0)
    chosen = []
    while len(pool):
        if pick == 'random':
            o = pool[rng.integers(len(pool))]
        else:
            o = pool[rng.integers(len(pool))]
        chosen.append(int(o))
        pool = pool[pool != o]
        if len(pool) == 0: break
        ok = compat_row(o, pool, Rall, MN, MD)
        pool = pool[ok]
    return chosen
if __name__ == '__main__':
    side = sys.argv[1]; trials = int(sys.argv[2]); seed = int(sys.argv[3])
    res = pickle.load(open('/home/user/degree-diameter/research/squads/beyond-small/r3/e07/horbs.pkl','rb'))
    orbs = res[side]
    t0 = time.time()
    Rall, MN, MD = prep(side, orbs)
    # self-compat pool is already filtered; orbits self-disjoint
    rng = np.random.default_rng(seed)
    best = []; hist = {}
    for tr in range(trials):
        ch = greedy(list(range(len(orbs))), Rall, MN, MD, rng)
        hist[len(ch)] = hist.get(len(ch),0)+1
        if len(ch) > len(best): best = ch
        if time.time()-t0 > 60: break
    print('side', side, 'trials', tr+1, 'hist', sorted(hist.items()), 'best H-orbits', len(best),
          'hubs', 66*len(best), 'time', round(time.time()-t0,1), flush=True)
    pickle.dump([orbs[i][0] for i in best], open(f'/home/user/degree-diameter/research/squads/beyond-small/r3/e07/best_{side}_seed{seed}.pkl','wb'))
