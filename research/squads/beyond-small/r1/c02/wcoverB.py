# Weighted local search for a B-side hub set M (<= 17 A-vertices, distinct (i,x) keys) whose distance-<=3
# balls cover ALL of B.  Uses MT[a, w] (A-vertex a within distance 3 of B-vertex nA+w).  usage: STATE K SECONDS
import numpy as np, sys, os, time, json
t0 = time.time()
STATE = sys.argv[1]; K = int(sys.argv[2]); SECS = float(sys.argv[3])
MTP = '/home/user/degree-diameter/research/squads/beyond-small/r1/c02/MT.npy'
MT = np.load(MTP)
nA = nB = 16896
key = (np.arange(nA) >> 8) // 22 * 256 + (np.arange(nA) & 255)
rng = np.random.default_rng(int(time.time()*1000) % 2**31)
if os.path.exists(STATE):
    st = json.load(open(STATE)); M = st['M']; wt = np.array(st['wt'], dtype=np.int64)
    tabu = np.array(st['tabu'], dtype=np.int64); it = st['it']; bestu = st['bestu']; bestM = st['bestM']
else:
    M = [int(x) for x in rng.choice(nA, K, replace=False)]; wt = np.ones(nB, dtype=np.int64)
    tabu = np.zeros(nA, dtype=np.int64); it = 0; bestu = None; bestM = None
cnt = MT[M].sum(axis=0, dtype=np.int64)
while time.time() - t0 < SECS:
    unc = cnt == 0
    nunc = int(unc.sum())
    if bestu is None or nunc < bestu: bestu, bestM = nunc, [int(x) for x in M]
    if nunc == 0: break
    cost = int(wt[unc].sum())
    best = None
    for i in range(K):
        cnt_i = cnt - MT[M[i]]
        Ui = np.nonzero(cnt_i == 0)[0]
        Wi = int(wt[Ui].sum())
        sc = (MT[:, Ui].astype(np.float32) @ wt[Ui].astype(np.float32)).astype(np.int64)
        others = [a for j, a in enumerate(M) if j != i]
        bad = np.isin(key, key[others]) | (tabu > it)
        bad[others] = True
        sc = np.where(bad, -10**12, sc)
        c = int(np.argmax(sc))
        newcost = Wi - int(sc[c])
        if best is None or newcost < best[0]: best = (newcost, i, c)
    newcost, i, c = best
    if newcost >= cost:
        wt[unc] += 1
    tabu[M[i]] = it + int(rng.integers(5, 25))
    cnt = cnt - MT[M[i]] + MT[c]
    M[i] = c
    it += 1
    if it % 10 == 0: print('it', it, 'uncovered B', int((cnt == 0).sum()), 'best', bestu, 'elapsed', round(time.time()-t0, 1), flush=True)
json.dump({'M': [int(x) for x in M], 'wt': wt.tolist(), 'tabu': tabu.tolist(), 'it': it, 'bestu': bestu, 'bestM': bestM},
          open(STATE, 'w'))
print('it', it, 'current uncovered B', int((cnt == 0).sum()), 'best', bestu, 'bestM', bestM, flush=True)
