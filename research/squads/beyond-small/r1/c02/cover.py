# Tabu search: choose N (<=17 B-vertices, pairwise distinct (j,y) so that the 22 translates are disjoint)
# minimising the number of A-vertices NOT within distance 3 of N.  usage: cover.py STATEFILE K ITERS
import numpy as np, sys, os, time, json
t0 = time.time()
balls = np.load('ball3B.npy')            # (16896, 2112) packed A-coverage bitsets, row w = B-index w
nB = balls.shape[0]
LUT = np.array([bin(i).count('1') for i in range(256)], dtype=np.int32)
w = np.arange(nB)
key = (w >> 8) // 22 * 256 + (w & 255)   # (j, y): translates by h-shift share the key
K = int(sys.argv[2]); ITERS = int(sys.argv[3]); STATE = sys.argv[1]
rng = np.random.default_rng(int(time.time()) % 1000)
nA = balls.shape[1] * 8
def popc(rows_packed):
    return np.bitwise_count(rows_packed).sum(axis=-1, dtype=np.int64)
def covered(N):
    c = np.zeros(balls.shape[1], dtype=np.uint8)
    for b in N: c |= balls[b]
    return c
if os.path.exists(STATE):
    st = json.load(open(STATE)); N = st['N']; tabu = np.array(st['tabu'], dtype=np.int64); it0 = st['it']; best = st['best']; st_bestN = st['bestN']
else:
    # greedy start
    N = []; U = np.full(balls.shape[1], 255, dtype=np.uint8)
    for _ in range(K):
        gain = popc(balls & U)
        keys = set(key[N]) if N else set()
        ok = np.array([k not in keys for k in key])
        gain = np.where(ok, gain, -1)
        if N: gain[N] = -1
        c = int(np.argmax(gain)); N.append(c); U &= ~balls[c]
    tabu = np.zeros(nB, dtype=np.int64); it0 = 0; best = None; st_bestN = None
TENURE = 40
STALL = 0
bestN = st_bestN if 'st_bestN' in dir() else None; bestcost = best
for it in range(it0, it0 + ITERS):
    cov = covered(N)
    unc = popc(~cov[None, :] & np.uint8(255))  # placeholder not used
    # cost
    U = (~cov) & np.uint8(255)
    cost = int(LUT[U].sum())
    if bestcost is None or cost < bestcost: bestcost, bestN = cost, [int(x) for x in N]
    if cost == 0: break
    cand_best = None
    keys_all = key
    for i in range(K):
        others = [b for j, b in enumerate(N) if j != i]
        cov_i = covered(others)
        Ui = (~cov_i) & np.uint8(255)            # uncovered if b_i removed
        Ui = Ui & np.uint8(255)
        base = int(LUT[Ui].sum())
        gain = popc(balls & Ui)                  # newly covered by candidate
        okkey = np.ones(nB, dtype=bool)
        okkey &= ~np.isin(key, key[others]) if others else True
        okkey &= (tabu <= it)
        okkey[N] = False
        g = np.where(okkey, gain, -1)
        c = int(np.argmax(g))
        newcost = base - int(g[c])
        if cand_best is None or newcost < cand_best[0]:
            cand_best = (newcost, i, c)
    newcost, i, c = cand_best
    tabu[N[i]] = it + int(rng.integers(15, 60))
    N[i] = c
    if it % 5 == 0 or True: print('it', it, 'cost', newcost, 'best', bestcost, 'elapsed', round(time.time()-t0,1), flush=True)
    if time.time() - t0 > 80: it += 1; break
json.dump({'N': [int(x) for x in N], 'tabu': tabu.tolist(), 'it': it + 1, 'best': bestcost,
           'bestN': [int(x) for x in bestN]}, open(STATE, 'w'))
print('state saved; current cost', newcost if 'newcost' in dir() else None, 'best cost', bestcost, 'bestN', bestN, flush=True)
