import random, math
import numpy as np
import networkx as nx
import sp
from sp import COL, NP


def conflict_matrix(orbs):
    n = len(orbs)
    Mo = np.zeros((n, NP), dtype=np.int64)
    for i, o in enumerate(orbs):
        Mo[i, o] = 1
    C = (Mo @ COL.astype(np.int64) @ Mo.T) > 0
    np.fill_diagonal(C, False)
    return C


def mwis_ils(w, C, iters=200000, seed=0, T0=0.6, tenure=7):
    """weighted independent set local search on conflict matrix C (bool n x n). Returns (weight, list)."""
    rnd = random.Random(seed)
    n = len(w)
    nbr = [np.nonzero(C[i])[0].tolist() for i in range(n)]
    inS = [False] * n
    conf_cnt = [0] * n
    tabu = [0] * n
    st = {'wt': 0}
    def add(v):
        inS[v] = True; st['wt'] += w[v]
        for u in nbr[v]: conf_cnt[u] += 1
    def rem(v):
        inS[v] = False; st['wt'] -= w[v]
        for u in nbr[v]: conf_cnt[u] -= 1
    order = list(range(n)); rnd.shuffle(order)
    for v in order:
        if not inS[v] and conf_cnt[v] == 0: add(v)
    best = (st['wt'], [v for v in range(n) if inS[v]])
    for it in range(iters):
        T = T0 * (1 - it / iters) + 0.05
        v = rnd.randrange(n)
        if inS[v] or tabu[v] > it: continue
        removed = [u for u in nbr[v] if inS[u]]
        delta = w[v] - sum(w[u] for u in removed)
        if delta >= 0 or rnd.random() < math.exp(delta / T):
            for u in removed:
                rem(u); tabu[u] = it + tenure + rnd.randrange(5)
            add(v)
            if st['wt'] > best[0]:
                best = (st['wt'], [x for x in range(n) if inS[x]])
    return best


def max_union(orbs, iters=200000, seed=0, exact_n=60):
    good = [o for o in orbs if not sp.collinear_pairs_inside(o)]
    n = len(good)
    if n == 0:
        return 0, [], False
    C = conflict_matrix(good)
    w = [len(o) for o in good]
    exact = False
    if n <= exact_n:
        g = nx.Graph()
        for i in range(n): g.add_node(i, weight=w[i])
        for i in range(n):
            for j in range(i + 1, n):
                if not C[i, j]: g.add_edge(i, j)
        cl, _ = nx.max_weight_clique(g, weight='weight')
        ch = cl; exact = True
    else:
        _, ch = mwis_ils(w, C, iters=iters, seed=seed)
    pts = sorted(int(p) for i in ch for p in good[i])
    assert not COL[np.ix_(pts, pts)].any()
    return len(pts), pts, exact
