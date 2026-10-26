"""Step 1-2 of card c9: balanced proper 7-colouring of the line-concurrence graph of H(5) (equitable tabu swap search).
Writes colours (c(l) in 1..7 as Z_8 values) and e(p) (missing colour at p) to colours_q5.npz."""
import sys, time
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d10D8_work')
from hexlib import load

q = 5
K = 7                       # colours = nonzero elements of Z_{q+3}
N, LP, PL, coord = load(q)
nbr = np.zeros((N, 30), dtype=np.int64)
for l in range(N):
    s = sorted({int(l2) for p in LP[l] for l2 in PL[p] if l2 != l})
    assert len(s) == 30, len(s)
    nbr[l] = s
A = np.zeros((N, N), dtype=np.uint8)
A[np.arange(N)[:, None], nbr] = 1

rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
TL = float(sys.argv[2]) if len(sys.argv) > 2 else 240.0
col = rng.permutation(np.repeat(np.arange(K), N // K))
conf = np.zeros((N, K), dtype=np.int64)
for k in range(30):
    conf[np.arange(N), col[nbr[:, k]]] += 1
tabu = np.zeros((N, K), dtype=np.int64)
idx = np.arange(N)

def nconf():
    return int(conf[idx, col].sum() // 2)

cur = nconf(); best = cur
t0 = time.time(); it = 0
while cur > 0 and time.time() - t0 < TL:
    it += 1
    C = np.nonzero(conf[idx, col] > 0)[0]
    cand_u = rng.choice(C, size=min(8, len(C)), replace=False)
    bestd = None; bestmv = None
    for u in cand_u:
        a = col[u]
        cols = col
        d = conf[u, cols] - conf[u, a] + conf[idx, a] - conf[idx, cols] - 2 * A[u].astype(np.int64)
        ok = (cols != a) & ((tabu[u, cols] <= it) & (tabu[idx, a] <= it))
        # aspiration: allow tabu moves if they reach a new best
        asp = (cur + d < best)
        d = np.where(ok | (asp & (cols != a)), d, 10**9)
        w = int(np.argmin(d + rng.random(N) * 0.5))
        if bestd is None or d[w] < bestd:
            bestd = d[w]; bestmv = (int(u), w)
    u, w = bestmv
    a, b = col[u], col[w]
    for x in nbr[u]:
        conf[x, a] -= 1; conf[x, b] += 1
    for y in nbr[w]:
        conf[y, b] -= 1; conf[y, a] += 1
    col[u], col[w] = b, a
    tabu[u, a] = it + 7 + rng.integers(0, 10)
    tabu[w, b] = it + 7 + rng.integers(0, 10)
    cur = nconf()
    if cur < best:
        best = cur
    if it % 2000 == 0:
        print(f'it {it} conf {cur} best {best} t {time.time()-t0:.0f}s', flush=True)

print('done it', it, 'final conflicts', cur, 'best', best, 'class sizes', np.bincount(col, minlength=K).tolist(), flush=True)
if cur == 0:
    # missing colour at each point
    e = np.zeros(N, dtype=np.int64)
    for p in range(N):
        seen = set(int(col[l]) for l in PL[p])
        assert len(seen) == q + 1
        e[p] = [c for c in range(K) if c not in seen][0]
    np.savez('/home/user/degree-diameter/research/squads/r1_d8c/c9/colours_q5.npz', col=col, e=e)
    print('saved; e class sizes', np.bincount(e, minlength=K).tolist())
