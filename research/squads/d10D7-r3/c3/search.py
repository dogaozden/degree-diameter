# Card c3, step 2: simulated-annealing swap search on M (points -> lines, M[p_k] = l_k fixed) minimising the total
# number of uncovered opposite targets over all pairs and both sides, with an exact incremental evaluator:
# per pair k and side, a count of routes covering each target; a swap of M(u1), M(u2) only re-evaluates the routes of
# u1, u2 (side A, pairs k with d(p_k,u) in {2,4}) and of their lines L1, L2 (side B, pairs k with d(l_k,L) in {2,4}).
# Moves: with prob ptar a targeted move (pick an uncovered target x of pair k, a line L through x at distance 5 from
# p_k, and a point u in D4(p_k); swap M(u) with the current preimage of L), else a uniform random swap.
# usage: search.py START.npy OUT.npy SECONDS SEED T0 T1 PTAR
import sys, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D7-r3/tools')
import numpy as np
from hexkit import Hex
HERE = '/home/user/degree-diameter/research/squads/d10D7-r3/c3'
start, out, seconds, seed = sys.argv[1], sys.argv[2], float(sys.argv[3]), int(sys.argv[4])
T0, T1, ptar = float(sys.argv[5]), float(sys.argv[6]), float(sys.argv[7])
H = Hex(8); N = H.N; LP = H.LP; PL = H.PL
F = [tuple(map(int, r)) for r in np.load(HERE + '/F21.npy')]; K = len(F)
freedP = np.zeros(N, bool); freedP[[p for p, l in F]] = True
M = np.load(start).astype(np.int64).copy()
Minv = np.empty(N, np.int64); Minv[M] = np.arange(N)
Dp = [H.bfs(p) for p, l in F]; Dl = [H.bfs(l, True) for p, l in F]
oppA = [Dp[k][:N] == 6 for k in range(K)]; oppB = [Dl[k][N:] == 6 for k in range(K)]
D4 = [np.nonzero((Dp[k][:N] == 4) & ~freedP)[0] for k in range(K)]
D4L = [np.nonzero(Dl[k][N:] == 4)[0] for k in range(K)]
relA = [[] for _ in range(N)]; relB = [[] for _ in range(N)]
for k in range(K):
    for u in np.nonzero((Dp[k][:N] == 2) | (Dp[k][:N] == 4))[0]: relA[u].append(k)
    for L in np.nonzero((Dl[k][N:] == 2) | (Dl[k][N:] == 4))[0]: relB[L].append(k)
cA = [np.zeros(N, np.int32) for _ in range(K)]; cB = [np.zeros(N, np.int32) for _ in range(K)]

def routeA(k, u):
    if freedP[u]: return None
    dk = Dp[k]; L = M[u]; d = dk[u]
    if d == 4: return LP[L] if dk[N + L] == 5 else None
    if d == 2: return np.unique(LP[PL[LP[L]]])          # points within distance 3 of line M(u)
    return None

def routeB(k, L):
    dk = Dl[k]; d = dk[N + L]
    if d != 4 and d != 2: return None
    y = Minv[L]
    if freedP[y]: return None
    if d == 4: return PL[y] if dk[y] == 5 else None
    return np.unique(PL[LP[PL[y]]])                      # lines within distance 3 of point M^-1(L)

def app(cnt, opp, r, s):
    if r is None: return 0
    c = cnt[r]
    if s > 0:
        dh = -int(np.count_nonzero((c == 0) & opp[r])); cnt[r] = c + 1
    else:
        dh = int(np.count_nonzero((c == 1) & opp[r])); cnt[r] = c - 1
    return dh

total = sum(int(oppA[k].sum()) + int(oppB[k].sum()) for k in range(K))
for u in range(N):
    for k in relA[u]: total += app(cA[k], oppA[k], routeA(k, u), +1)
for L in range(N):
    for k in relB[L]: total += app(cB[k], oppB[k], routeB(k, L), +1)
U = H.uncovered(F, M); full0 = sum(a + b for a, b in U)
print('start incremental', total, 'full', full0, flush=True); assert total == full0

def swap(u1, u2):
    if u1 == u2: return 0
    L1 = M[u1]; L2 = M[u2]; d = 0
    for u in (u1, u2):
        for k in relA[u]: d += app(cA[k], oppA[k], routeA(k, u), -1)
    for L in (L1, L2):
        for k in relB[L]: d += app(cB[k], oppB[k], routeB(k, L), -1)
    M[u1] = L2; M[u2] = L1; Minv[L1] = u2; Minv[L2] = u1
    for u in (u1, u2):
        for k in relA[u]: d += app(cA[k], oppA[k], routeA(k, u), +1)
    for L in (L1, L2):
        for k in relB[L]: d += app(cB[k], oppB[k], routeB(k, L), +1)
    return d

rng = np.random.default_rng(seed)
nonfree = np.nonzero(~freedP)[0]; nf = len(nonfree)

def targeted():
    k = int(rng.integers(K))
    if rng.random() < 0.5:
        cand = np.nonzero(oppA[k] & (cA[k] == 0))[0]
        if len(cand) == 0: return None
        x = int(cand[rng.integers(len(cand))])
        lines = [int(L) for L in PL[x] if Dp[k][N + L] == 5]
        L = lines[int(rng.integers(len(lines)))]
        uL = int(Minv[L])
        if freedP[uL]: return None
        u = int(D4[k][rng.integers(len(D4[k]))])
        return None if u == uL else (u, uL)
    cand = np.nonzero(oppB[k] & (cB[k] == 0))[0]
    if len(cand) == 0: return None
    t = int(cand[rng.integers(len(cand))])
    pts = [int(y) for y in LP[t] if Dl[k][y] == 5 and not freedP[y]]
    if not pts: return None
    y = pts[int(rng.integers(len(pts)))]
    L = int(D4L[k][rng.integers(len(D4L[k]))])
    uL = int(Minv[L])
    if freedP[uL]: return None
    return None if uL == y else (y, uL)

best = total; bestM = M.copy(); t0 = time.time(); acc = 0; it = 0; lastp = t0
while True:
    el = time.time() - t0
    if el > seconds: break
    T = T0 * (T1 / T0) ** (el / seconds)
    it += 1
    mv = targeted() if rng.random() < ptar else None
    if mv is None:
        mv = (int(nonfree[rng.integers(nf)]), int(nonfree[rng.integers(nf)]))
    d = swap(*mv)
    if d <= 0 or rng.random() < np.exp(-d / T):
        acc += 1
        if total + d < best: best = total + d; bestM = M.copy()
        total += d
    else:
        swap(*mv)
    if time.time() - lastp > 30:
        lastp = time.time(); print('t', int(el), 'it', it, 'acc', round(acc / it, 3), 'T', round(T, 3), 'cur', total, 'best', best, flush=True)
np.save(out, bestM)
Mv = bestM
assert len(set(Mv.tolist())) == N and all(Mv[p] == l for p, l in F)
Uf = H.uncovered(F, Mv); fin = sum(a + b for a, b in Uf)
print('iters', it, 'accepted', acc, 'best incremental', best, 'FULL CHECK total', fin, 'per pair', Uf, flush=True)
