"""Exact exchange neighbourhood of a fibre set K in the fibre model: for every removal set S of size <= SMAX
and every clique T of vertices outside K whose K-conflicts all lie in S, evaluate F = 11|K'| + free(K'),
K' = (K - S) + T.  Reports the best F and conflict-count statistics.  usage: exact_exch.py MODEL SMAX [TMAX]"""
import sys, itertools, numpy as np
from collections import Counter
sys.path.insert(0, '.')
import exact_local as EL
q = 11
ALL, R, ELL, vid, diff_index = EL.ALL, EL.R, EL.ELL, EL.vid, EL.diff_index
NF = EL.NF
K = [vid(*f) for f in EL.load_fibres(sys.argv[1])]
SMAX = int(sys.argv[2]); TMAX = int(sys.argv[3]) if len(sys.argv) > 3 else 6
k = len(K)
notK = np.ones(NF, bool); notK[K] = False
Dm = np.stack([R[diff_index(None, w)] for w in K], axis=1)  # NF x k: R(x - K_j)
conflict = Dm > 0
M = np.zeros(NF, dtype=np.int64)
for j in range(k): M |= (conflict[:, j].astype(np.int64) << j)
pc = conflict.sum(axis=1)
print('K size', k, ' outside-vertex conflict histogram (count of K-members in conflict):',
      sorted(Counter(pc[notK].tolist()).items())[:12], flush=True)
def free_of(Kl):
    cov = np.zeros((122, q), dtype=bool)
    rows = np.arange(122)
    for v in Kl:
        cov[rows, ELL[:, v]] = True
    return int((~cov.all(axis=1)).sum())
def compat_pair(i, j):
    return R[vid(*((ALL[i] - ALL[j]) % q))] == 0
best = [11 * k + free_of(K), None]
nevals = 0; counts = Counter()
t0 = np.array([0])
for ssz in range(1, SMAX + 1):
    for Sidx in itertools.combinations(range(k), ssz):
        Smask = 0
        for j in Sidx: Smask |= (1 << j)
        cand = np.nonzero(notK & ((M & ~np.int64(Smask)) == 0))[0]
        if len(cand) == 0: continue
        cand = cand.tolist()
        base = [K[j] for j in range(k) if j not in Sidx]
        # enumerate cliques T among cand (pairwise compatible), |T| <= TMAX
        stack = [([], 0)]
        while stack:
            T, start = stack.pop()
            if T:
                Kp = base + T
                F = 11 * len(Kp) + free_of(Kp); nevals += 1
                counts[len(T) - ssz] += 1
                if F > best[0]:
                    best = [F, (Sidx, tuple(T))]
                    print('NEW BEST F =', F, 'k =', len(Kp), 'remove', Sidx, 'add', T, flush=True)
            if len(T) >= TMAX: continue
            for ii in range(start, len(cand)):
                v = cand[ii]
                if all(compat_pair(v, u) for u in T):
                    stack.append((T + [v], ii + 1))
print('evaluated exchanges:', nevals, ' (|T|-|S| : count)', sorted(counts.items()))
print('best F found in exchange neighbourhood (S<=%d):' % SMAX, best[0], best[1] if best[1] else '(none better than the start)')
