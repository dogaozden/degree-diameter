"""Unbalanced TabuCol (single-vertex moves) for a proper 7-colouring of the H(5) line-concurrence graph; diagnostic
for card c9 step 1. Saves the colouring if it reaches 0 conflicts, then reports class sizes."""
import sys, time
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d10D8_work')
from hexlib import load
N, LP, PL, coord = load(5)
K = 8
nbr = np.zeros((N, 30), dtype=np.int64)
for l in range(N):
    nbr[l] = sorted({int(l2) for p in LP[l] for l2 in PL[p] if l2 != l})
rng = np.random.default_rng(int(sys.argv[1])); TL = float(sys.argv[2])
col = rng.integers(0, K, N)
conf = np.zeros((N, K), dtype=np.int64)
for k in range(30):
    conf[np.arange(N), col[nbr[:, k]]] += 1
tabu = np.zeros((N, K), dtype=np.int64)
idx = np.arange(N)
cur = int(conf[idx, col].sum() // 2); best = cur; t0 = time.time(); it = 0
while cur > 0 and time.time() - t0 < TL:
    it += 1
    C = np.nonzero(conf[idx, col] > 0)[0]
    delta = conf[C] - conf[C, col[C]][:, None]          # (|C|, K)
    ok = (tabu[C] <= it) | (cur + (conf[C] - conf[C, col[C]][:, None]) // 1 < best)  # aspiration (approx)
    d = np.where(ok, delta, 10**6) + rng.random(delta.shape) * 0.5
    d[np.arange(len(C)), col[C]] = 10**6
    i, c = np.unravel_index(np.argmin(d), d.shape)
    v = C[i]; a = col[v]
    for x in nbr[v]:
        conf[x, a] -= 1; conf[x, c] += 1
    col[v] = c
    tabu[v, a] = it + 10 + rng.integers(0, 10)
    cur = int(conf[idx, col].sum() // 2); best = min(best, cur)
    if it % 5000 == 0:
        print(f'it {it} conf {cur} best {best} t {time.time()-t0:.0f}', flush=True)
print('end it', it, 'conf', cur, 'best', best, 'class sizes', np.bincount(col, minlength=K).tolist(), flush=True)
if cur == 0:
    np.save('/home/user/degree-diameter/research/squads/r1_d8c/c9/proper8_check.npy', col)
