"""simple local search for a large independent set (tabu-like swaps), numpy adjacency"""
import numpy as np, random
def local_indep(adj, iters=20000, seed=0, target=None):
    rng = random.Random(seed)
    n = adj.shape[0]
    nbrs = [np.nonzero(adj[i])[0].tolist() for i in range(n)]
    S = set(); conf = np.zeros(n, dtype=int)   # conf[v] = # neighbours in S
    best = set()
    tabu = np.zeros(n, dtype=int)
    for it in range(iters):
        free = [v for v in range(n) if v not in S and conf[v] == 0]
        if free:
            v = rng.choice(free); S.add(v)
            for w in nbrs[v]: conf[w] += 1
        else:
            # swap: pick vertex with conf==1 not tabu, remove its neighbour in S
            cands = [v for v in range(n) if v not in S and conf[v] == 1 and tabu[v] <= it]
            if not cands:
                cands = [v for v in range(n) if v not in S and tabu[v] <= it]
            v = rng.choice(cands)
            for u in nbrs[v]:
                if u in S:
                    S.remove(u)
                    for w in nbrs[u]: conf[w] -= 1
                    tabu[u] = it + 7
            S.add(v)
            for w in nbrs[v]: conf[w] += 1
        if len(S) > len(best):
            best = set(S)
            if target and len(best) >= target: break
    return sorted(best)
