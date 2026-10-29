# maximum partial ovoid (pairwise opposite points) of H(q) = max independent set in the conflict graph (d_coll<=2),
# found by fixed-k min-conflicts tabu search, k increased on success.
import sys, time
from common import *
q = int(sys.argv[1]); secs = float(sys.argv[2]); seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
rng = np.random.default_rng(seed)
q, N, LP, PL, col, conf = setup(q)
A = np.zeros((N, N), dtype=np.int32)
for p in range(N):
    A[p, conf[p]] = 1
def tabu_k(k, iters, S0=None):
    inS = np.zeros(N, bool)
    if S0 is None:
        S = rng.choice(N, k, replace=False)
    else:
        S = list(S0)
        extra = [v for v in rng.permutation(N) if v not in set(S)][:k - len(S)]
        S = np.array(list(S) + extra)
    inS[S] = True
    c = A[inS].sum(0).astype(np.int64)
    tabu = np.zeros(N, np.int64)
    best_f = None
    for it in range(iters):
        f = c[inS].sum() // 2
        if f == 0:
            return inS.copy(), 0
        # pick conflicting u in S: max c, non-tabu
        cu = np.where(inS, c, -1)
        cand = np.flatnonzero(cu == cu.max())
        u = rng.choice(cand)
        # pick v outside S with min c - A[u,v] (non tabu)
        score = c - A[u]
        mask = (~inS) & (tabu <= it)
        if not mask.any():
            mask = ~inS
        sc = np.where(mask, score, 10**9)
        m = sc.min()
        vs = np.flatnonzero(sc == m)
        v = rng.choice(vs)
        inS[u] = False; c -= A[u]
        inS[v] = True; c += A[v]
        tabu[u] = it + 7 + rng.integers(0, 10)
        tabu[v] = it + 3 + rng.integers(0, 3)
    return inS.copy(), int(c[inS].sum() // 2)
t0 = time.time()
k = 1
best = None
S = None
while time.time() - t0 < secs:
    res, f = tabu_k(k, 20000, None if S is None else np.flatnonzero(S))
    if f == 0:
        S = res
        best = np.flatnonzero(S)
        print(f'k={k} found, t={time.time()-t0:.1f}s', flush=True)
        k += 1
    else:
        print(f'k={k} failed (f={f}), t={time.time()-t0:.1f}s', flush=True)
        if time.time() - t0 > secs: break
        # keep trying same k a few times
        for _ in range(2):
            res, f = tabu_k(k, 20000, np.flatnonzero(S) if S is not None else None)
            if f == 0:
                S = res; best = np.flatnonzero(S); k += 1; break
        else:
            break
print('BEST partial ovoid size', len(best), sorted(best.tolist()))
np.save(f'/home/user/degree-diameter/research/squads/conics2-r1/c8/pov_q{q}_s{seed}.npy', best)
