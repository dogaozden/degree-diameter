#!/usr/bin/env python3
"""extend.py IN OUT ITERS SEED : grow a valid point set of Q(6,11) over ALL 177156 points by greedy additions and
(1,1)-swaps (plateau moves), keeping pairwise non-orthogonality.  Writes the best set found to OUT."""
import sys, random, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d14D7-r5/c7')
from genpts import all_points
q = 11
inp, out, iters, seed = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
rng = random.Random(seed)
X = all_points()                     # 177156 x 7 singular normalized points
G = np.zeros((7, 7), dtype=np.int64)
for i, j in ((0, 4), (1, 5), (2, 6)): G[i, j] = G[j, i] = 1
G[3, 3] = -2
XG = (X @ G) % q                     # B(x,y) = (XG[x] . y) mod q
S0 = np.loadtxt(inp, dtype=np.int64, comments='#', ndmin=2) % q
def key(v):
    v = np.array(v); f = np.argmax(v != 0, axis=-1); s = np.take_along_axis(v, f[..., None], -1)[..., 0]
    inv = np.array([0] + [pow(i, q - 2, q) for i in range(1, q)])
    return (v * inv[s][..., None]) % q
index = {tuple(r): i for i, r in enumerate(X)}
S = set(index[tuple(r)] for r in key(S0))
assert len(S) == len(S0), 'input not normalized/distinct'
def brow(j):  # boolean vector: B(x, X[j]) == 0 over all points
    return (XG @ X[j]) % q == 0
cnt = np.zeros(len(X), dtype=np.int64)
for s in S: cnt += brow(s)
best = set(S)
def conflict_free(): return [i for i in range(len(X)) if i not in S and cnt[i] == 0]
tabu = {}
it = 0
free = conflict_free()
print('start', len(S), 'free', len(free), flush=True)
while it < iters:
    it += 1
    free = [i for i in np.flatnonzero((cnt == 0)) if i not in S]
    if free:
        x = rng.choice(free); S.add(x); cnt += brow(x)
        if len(S) > len(best): best = set(S); print('  size', len(best), 'it', it, flush=True)
        continue
    ones = [i for i in np.flatnonzero(cnt == 1) if i not in S and tabu.get(i, -1) < it]
    if not ones: 
        # perturb: drop a random point
        s = rng.choice(list(S)); S.remove(s); cnt -= brow(s); tabu[s] = it + 20
        continue
    x = rng.choice(ones)
    # find its unique conflicting member of S
    bx = brow(x)
    cands = [s for s in S if bx[s]]
    s = cands[0]
    S.remove(s); cnt -= brow(s); tabu[s] = it + 15
    S.add(x); cnt += brow(x)
    if len(S) > len(best): best = set(S); print('  size', len(best), 'it', it, flush=True)
np.savetxt(out, X[sorted(best)], fmt='%d')
print('best', len(best), 'written', out)
