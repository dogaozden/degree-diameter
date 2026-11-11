# Weighted tabu local search for the cover: N = 17 B-vertices (distinct (j,y)), uncovered A-vertices weighted.
# Element weights grow on local minima (configuration-weighting).  usage: wcover.py STATE K SECONDS
import numpy as np, sys, os, time, json
t0 = time.time()
EDGES = '/home/user/degree-diameter/research/squads/beyond-small/data/d16D5_n33792.edges'
K = int(sys.argv[2]); SECS = float(sys.argv[3]); STATE = sys.argv[1]
nA = 16896; nB = 16896
MT = np.zeros((nA, nB), dtype=np.uint8)     # MT[a, w] = 1 iff B-vertex (nA + w) is within distance 3 of a
if not os.path.exists('/home/user/degree-diameter/research/squads/beyond-small/r1/c02/MT.npy'):
    with open(EDGES) as f:
        n = int(f.readline()); E = np.loadtxt(f, dtype=np.int64)
    adj = np.full((n, 16), -1, dtype=np.int64); deg = np.zeros(n, dtype=np.int64)
    for u, v in E:
        adj[u, deg[u]] = v; deg[u] += 1; adj[v, deg[v]] = u; deg[v] += 1
    for a in range(nA):
        N1 = adj[a]; N2 = np.unique(adj[N1].ravel()); N3 = np.unique(adj[N2].ravel())
        MT[a, np.concatenate([N1, N3]) - nA] = 1
    np.save('/home/user/degree-diameter/research/squads/beyond-small/r1/c02/MT.npy', MT)
else:
    MT = np.load('/home/user/degree-diameter/research/squads/beyond-small/r1/c02/MT.npy')
w_idx = np.arange(nB)
key = (w_idx >> 8) // 22 * 256 + (w_idx & 255)
rng = np.random.default_rng(int(time.time()*1000) % 2**31)
if os.path.exists(STATE):
    st = json.load(open(STATE)); N = st['N']; wt = np.array(st['wt'], dtype=np.int64)
    tabu = np.array(st['tabu'], dtype=np.int64); it0 = st['it']; bestu = st['bestu']; bestN = st['bestN']
else:
    N = []; wt = np.ones(nA, dtype=np.int64); tabu = np.zeros(nB, dtype=np.int64); it0 = 0; bestu = None; bestN = None
    # greedy start
    cnt = np.zeros(nA, dtype=np.int64)
    for _ in range(K):
        unc = cnt == 0
        sc = MT[unc].sum(axis=0).astype(np.int64)
        sc[np.isin(key, key[N]) if N else np.zeros(nB, bool)] = -1
        if N: sc[N] = -1
        c = int(np.argmax(sc)); N.append(c); cnt += MT[:, c]
def counts(N):
    return MT[:, N].sum(axis=1, dtype=np.int64)
it = it0
cnt = counts(N)
while time.time() - t0 < SECS:
    unc = cnt == 0
    nunc = int(unc.sum())
    if bestu is None or nunc < bestu: bestu, bestN = nunc, [int(x) for x in N]
    if nunc == 0: break
    cost = int(wt[unc].sum())
    best = None
    for i in range(K):
        cnt_i = cnt - MT[:, N[i]]
        Ui = np.nonzero(cnt_i == 0)[0]
        Wi = int(wt[Ui].sum())
        sc = (wt[Ui].astype(np.float32) @ MT[Ui].astype(np.float32)).astype(np.int64)
        others = [b for j, b in enumerate(N) if j != i]
        bad = np.isin(key, key[others]) | (tabu > it)
        bad[others] = True
        sc = np.where(bad, -10**12, sc)
        c = int(np.argmax(sc))
        newcost = Wi - int(sc[c])
        if best is None or newcost < best[0]: best = (newcost, i, c)
    newcost, i, c = best
    if newcost >= cost:
        wt[unc] += 1                                  # local minimum: raise weights of uncovered elements
    tabu[N[i]] = it + int(rng.integers(5, 25))
    cnt = cnt - MT[:, N[i]] + MT[:, c]
    N[i] = c
    it += 1
    if it % 10 == 0: print('it', it, 'uncovered', int((cnt == 0).sum()), 'best', bestu, 'elapsed', round(time.time()-t0, 1), flush=True)
json.dump({'N': [int(x) for x in N], 'wt': wt.tolist(), 'tabu': tabu.tolist(), 'it': it, 'bestu': bestu, 'bestN': bestN},
          open(STATE, 'w'))
print('it', it, 'current uncovered', int((cnt == 0).sum()), 'best', bestu, 'bestN', bestN, flush=True)
