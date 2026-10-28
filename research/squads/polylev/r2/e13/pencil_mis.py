"""Max set of pairwise non-collinear points of H(q) (= disjoint pencils of lines), by k-fixed tabu search for an
independent set in the point collinearity graph. Usage: pencil_mis.py q SECONDS SEED OUT.npy [k0]
Writes the best independent set (point ids) found; it is verified (no two points on a common line)."""
import sys, time
import numpy as np
from common import *
q, secs, seed, out = int(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
rng = np.random.default_rng(seed)
H = load(q)
N = H.N
nbr = [set() for _ in range(N)]
for l in range(H.L):
    pts = H.lines[l].tolist()
    for a in pts:
        for b in pts:
            if a != b:
                nbr[a].add(b)
adj = [np.array(sorted(x), dtype=np.int64) for x in nbr]
def independent(S):
    s = set(S)
    return all(not (nbr[v] & s) for v in S)
# greedy start
order = rng.permutation(N)
S = []
blocked = np.zeros(N, bool)
for v in order:
    if not blocked[v]:
        S.append(int(v)); blocked[adj[v]] = True; blocked[v] = True
best = list(S)
k = len(S) + 1
t0 = time.time()
inS = np.zeros(N, bool)
def run_k(k, S, tmax):
    # S: list of k vertices (start from best + random)
    inS[:] = False
    inS[S] = True
    c = np.zeros(N, np.int64)
    for v in S:
        c[adj[v]] += 1
    tabu = np.zeros(N, np.int64)
    it = 0
    while time.time() - t0 < tmax:
        it += 1
        conf = np.array([v for v in S if c[v] > 0])
        f = int(c[np.array(S)].sum()) // 2
        if f == 0:
            return list(S)
        u = int(rng.choice(conf))
        cand = np.where((~inS) & (tabu <= it))[0]
        if len(cand) == 0:
            continue
        m = c[cand].min()
        cc = cand[c[cand] == m]
        v = int(rng.choice(cc))
        # swap u -> v
        inS[u] = False; c[adj[u]] -= 1
        inS[v] = True; c[adj[v]] += 1
        S[S.index(u)] = v
        tabu[u] = it + 7 + int(rng.integers(0, 10))
    return None
print('greedy', len(best), flush=True)
while time.time() - t0 < secs:
    # extend the best set by one random vertex with min conflicts
    start = list(best)
    cand = [v for v in range(N) if v not in start]
    v = int(rng.choice(cand))
    start = start + [v]
    res = run_k(len(start), start, secs)
    if res is not None and independent(res):
        best = res
        print('found independent set of size', len(best), 'at', round(time.time() - t0), 's', flush=True)
        np.save(out, np.array(best, dtype=np.int64))
    else:
        break
print('final', len(best), 'valid', independent(best), flush=True)
np.save(out, np.array(best, dtype=np.int64))
