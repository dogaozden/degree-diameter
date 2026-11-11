"""For low-cost Haar S (cost <= LIM) of a meta group: is each central involution missing from the far sets?"""
import sys, time, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/handsoff-49/w13')
from meta import *
from hc import cost_fn
m, k, r, secs, LIM = map(int, sys.argv[1:6]); seed = int(sys.argv[6])
T = meta_table(m, k, r); Sinv = inverses(T); N = T.shape[0]
# central involutions: x with x^2 = e and commuting with all generators (check against all elements via table)
ident = 0
sq = T[np.arange(N), np.arange(N)]
inv2 = np.nonzero(sq == ident)[0]; inv2 = inv2[inv2 != ident]
cen = [x for x in inv2 if np.all(T[x] == T[:, x])]
print("involutions", len(inv2), "central involutions", [(int(x % m), int(x // m)) for x in cen], flush=True)
rng = np.random.default_rng(seed)
stats = {}
zcount = {}
t0 = time.time(); found = 0; zin = {}
S = [0] + list(rng.choice(np.arange(1, N), 3, replace=False))
c, _, _ = cost_fn(T, Sinv, S)
while time.time() - t0 < secs:
    i = rng.integers(1, 4); x = int(rng.integers(1, N))
    if x in S: continue
    S2 = list(S); S2[i] = x
    c2, _, _ = cost_fn(T, Sinv, S2)
    if c2 <= c or rng.random() < np.exp(-(c2 - c) / 0.7):
        S, c = S2, c2
    if c <= LIM:
        Sa = np.array(S)
        TA = prodset(T, Sinv[Sa], Sa); TB = prodset(T, Sa, Sinv[Sa])
        PA = np.array([0]); PB = np.array([0])
        for _ in range(4):
            PA = prodset(T, PA, TA); PB = prodset(T, PB, TB)
        MA = set(np.setdiff1d(np.arange(N), PA).tolist()); MB = set(np.setdiff1d(np.arange(N), PB).tolist())
        found += 1
        key = c
        stats.setdefault(key, [0, 0])
        stats[key][0] += 1
        for z in cen:
            zc = zcount.setdefault(int(z), [0, 0])
            zc[0] += 1
            if z in MA or z in MB: zc[1] += 1
print("central involution -> (states, states where it is far on some side):", {(int(z%m), int(z//m)): v for z, v in zcount.items()})
print("low-cost states", found, "by cost (count, all central involutions far on some side):", sorted(stats.items()), flush=True)
