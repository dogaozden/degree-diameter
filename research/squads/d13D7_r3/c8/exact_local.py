"""Exact small-move check in the fibre model around a fibre set K (default: the 397 state).
For removals S (|S| <= SMAX) and additions T (|T| <= TMAX, all fibres outside K whose conflicts lie inside S,
pairwise compatible), evaluate F = 11|K'| + free(K') exactly, K' = (K - S) + T."""
import sys, itertools, numpy as np
q = 11
def load_fibres(path):
    fib = []
    for line in open(path):
        t = line.split()
        if t and t[0] == 'F': fib.append(tuple(int(z) for z in t[1:5]))
    return fib
def vid(s, b, c, f): return s + q*b + q*q*c + q*q*q*f
ALL = np.array([(s, b, c, f) for f in range(q) for c in range(q) for b in range(q) for s in range(q)])  # index = vid
NF = len(ALL)
# R[d]: roots of 9 dl^2 + ds dl + (db df - dc^2)
R = np.zeros(NF, dtype=np.int64)
for d in range(NF):
    s, b, c, f = ALL[d]
    if d == 0: R[d] = 0; continue
    R[d] = sum(1 for dl in range(q) if (9*dl*dl + s*dl + b*f - c*c) % q == 0)
# P list (122) and ell table
Pv = []
for x1 in range(q):
    for x2 in range(q):
        for x3 in range(q):
            for x6 in range(q):
                v = (x1, x2, x3, x6)
                if v == (0, 0, 0, 0): continue
                if (2*x1*x1 + x2*x6 - x3*x3) % q: continue
                if next(t for t in v if t) != 1: continue
                Pv.append(v)
assert len(Pv) == 122
Pv = np.array(Pv)
S_ = ALL[:, 0]; B_ = ALL[:, 1]; C_ = ALL[:, 2]; F_ = ALL[:, 3]
ELL = (Pv[:, 0:1]*S_[None, :] + Pv[:, 1:2]*F_[None, :] + Pv[:, 3:4]*B_[None, :] - 2*Pv[:, 2:3]*C_[None, :]) % q  # 122 x NF
def diff_index(v, w):
    """vector of indices of (x - w) for all x in ALL, given w index"""
    ws, wb, wc, wf = ALL[w]
    d = np.stack([(S_ - ws) % q, (B_ - wb) % q, (C_ - wc) % q, (F_ - wf) % q], axis=1)
    return d[:, 0] + q*d[:, 1] + q*q*d[:, 2] + q*q*q*d[:, 3]
def free_count(Kidx):
    if not Kidx: return 122
    vals = ELL[:, Kidx]  # 122 x k
    cover = np.zeros((122, q), dtype=bool)
    for j in range(len(Kidx)):
        cover[np.arange(122), vals[:, j]] = True
    return int((~cover.all(axis=1)).sum())
def compatible(i, j):
    return R[vid(*((ALL[i] - ALL[j]) % q))] == 0
if __name__ == '__main__':
    path = sys.argv[1]
    smax = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    tmax = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    K = [vid(*f) for f in load_fibres(path)]
    k = len(K)
    print('K size', k, 'F =', 11*k + free_count(K), 'free', free_count(K))
    # conflict sets of all vertices with K
    Kset = set(K)
    Dm = np.stack([R[diff_index(None, w)] for w in K], axis=1)  # NF x k  (R of x-w)
    conflicts = {}
    for v in range(NF):
        if v in Kset: continue
        N = tuple(j for j in range(k) if Dm[v, j] > 0)
        conflicts.setdefault(N, []).append(v)
    print('vertices outside K by conflict-set size:', {len(N): len(vs) for N, vs in conflicts.items() if len(N) <= 3 and True} )
    free_adds = conflicts.get((), [])
    print('conflict-free outside vertices (clique extensions of K):', len(free_adds))
    bestbox = [(free_count(K) + 11*k, None)]
    results = []
    for ssz in range(0, smax+1):
        for Sidx in itertools.combinations(range(k), ssz):
            Sset = set(Sidx)
            # candidate additions: conflicts inside S
            cand = []
            for N, vs in conflicts.items():
                if set(N) <= Sset: cand.extend(vs)
            if not cand: continue
            # max cliques among candidates of size up to tmax (greedy exhaustive via DFS)
            cand = sorted(set(cand))
            def dfs(T, start):
                kprime = [K[j] for j in range(k) if j not in Sset] + T
                if T:
                    F = 11*len(kprime) + free_count(kprime)
                    if F > bestbox[0][0]:
                        bestbox[0] = (F, (Sidx, tuple(T)))
                        print('NEW BEST F =', F, 'remove', Sidx, 'add', T, flush=True)
                    results.append((len(kprime), F))
                if len(T) >= tmax: return
                for ii in range(start, len(cand)):
                    v = cand[ii]
                    if all(compatible(v, u) for u in T):
                        dfs(T + [v], ii + 1)
            dfs([], 0)
    print('best found:', bestbox[0][0], bestbox[0][1])
    from collections import Counter
    byk = Counter(r[0] for r in results)
    print('evaluated (k_new: count):', sorted(byk.items()))
    for kk in sorted(set(r[0] for r in results)):
        print('  k=%d max F=%d' % (kk, max(r[1] for r in results if r[0] == kk)))
