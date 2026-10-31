"""How often does each group element lie in (S^-1 S)^4 for random S (e in S)?  Rare elements = structural obstacles."""
import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/handsoff-49/w13')
from meta import *
m, k, r, samples = map(int, sys.argv[1:5])
T = meta_table(m, k, r); Sinv = inverses(T); N = T.shape[0]
rng = np.random.default_rng(5)
hitA = np.zeros(N, int); hitB = np.zeros(N, int); both = np.zeros(N, int)
for it in range(samples):
    S = np.array([0] + list(rng.choice(np.arange(1, N), 3, replace=False)))
    TA = prodset(T, Sinv[S], S); TB = prodset(T, S, Sinv[S])
    PA = np.array([0]); PB = np.array([0])
    for _ in range(4):
        PA = prodset(T, PA, TA); PB = prodset(T, PB, TB)
    hitA[PA] += 1; hitB[PB] += 1
show = lambda x: (int(x % m), int(x // m))
order = np.argsort(hitA)
print("least often in T^4 (A side):")
for x in order[:12]: print(show(x), hitA[x], hitB[x])
print("hit-rate distribution A: min", hitA.min(), "median", int(np.median(hitA)), "max", hitA.max())
print("zero-hit count A", int((hitA == 0).sum()), "B", int((hitB == 0).sum()))
np.save(f"/home/user/degree-diameter/research/squads/handsoff-49/w13/freq_{m}_{k}_{r}.npy", np.vstack([hitA, hitB]))
