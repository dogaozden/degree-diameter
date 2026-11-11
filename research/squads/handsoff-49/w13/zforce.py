"""Anneal on Haar S of meta m k r, but force z reached (penalty if z is far): min cost among z-reached states."""
import sys, time, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/handsoff-49/w13')
from meta import *
from hc import cost_fn
m, k, r, secs, seed, z, pen = map(int, sys.argv[1:8])
T = meta_table(m, k, r); Sinv = inverses(T); N = T.shape[0]
rng = np.random.default_rng(seed)
def f(S):
    S = np.asarray(S)
    TA = prodset(T, Sinv[S], S); TB = prodset(T, S, Sinv[S])
    PA = np.array([0]); PB = np.array([0])
    for _ in range(4):
        PA = prodset(T, PA, TA); PB = prodset(T, PB, TB)
    c = (N - len(PA)) + (N - len(PB))
    zmiss = (z not in set(PA.tolist())) or (z not in set(PB.tolist()))
    return c + (pen if zmiss else 0), c, zmiss
S = [0] + list(rng.choice(np.arange(1, N), 3, replace=False))
cur, _, _ = f(S)
best = (10**9, None)
t0 = time.time()
while time.time() - t0 < secs:
    i = rng.integers(1, 4); x = int(rng.integers(1, N))
    if x in S: continue
    S2 = list(S); S2[i] = x
    v2, c2, zm2 = f(S2)
    temp = 1.5 * max(0.05, 1 - (time.time() - t0) / secs)
    if v2 <= cur or rng.random() < np.exp(-(v2 - cur) / temp):
        S, cur = S2, v2
        if not zm2 and c2 < best[0]:
            best = (c2, list(S))
print("min cost with z reached:", best[0], "S", best[1], flush=True)
