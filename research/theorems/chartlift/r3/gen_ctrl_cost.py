"""Score a general (non-voltage) controller for a chart that covers both diagonals with complete pencils (Theorem 11):
uncovered same-side pairs = pairs (u, u'), u' != u, that are neither at distance 2 nor joined by a nonbacktracking
4-walk with a nonsingular pattern.  Tries many proper k-edge-colourings (controller.proper_colouring seeds) and all
letter relabellings, for each chart flags file given.
usage: python3 r3/gen_ctrl_cost.py GRAPH.json k SEEDS FLAGS... (prints the best cost per flags file)"""
import sys, itertools
sys.path.insert(0, '.')
from controller import read_graph, proper_colouring
path, k, nseeds, flagfiles = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4:]
n, E = read_graph(path)
def load_flags(fp):
    f = [l for l in open(fp).read().split('\n') if l.strip()]
    assert int(f[0]) == k
    sing = [list(map(int, f[1].split())), list(map(int, f[2].split()))]
    pen = [list(map(int, f[3].split())), list(map(int, f[4].split()))]; dg = list(map(int, f[5].split()))
    assert all(pen[s][i * k + j] for s in range(2) for i in range(k) for j in range(k) if i != j) and dg == [1, 1], 'chart must have complete pencils and both diagonals'
    return sing
def code(p): return ((p[0] * k + p[1]) * k + p[2]) * k + p[3]
best = {fp: (10 ** 9, None) for fp in flagfiles}
SING = {fp: load_flags(fp) for fp in flagfiles}
perms = list(itertools.permutations(range(k)))
for seed in range(nseeds):
    As, Bs, ce = proper_colouring(n, E, k, seed)
    m = len(As)
    adjA = [[] for _ in range(m)]; adjB = [[] for _ in range(m)]
    for a, b, c in ce: adjA[a].append((b, c)); adjB[b].append((a, c))
    # enumerate walks once: for each side, start, the list of (end, colour pattern) of NB 4-walks, and 2-walk ends
    walks = [[], []]; two = [[], []]
    for side, (X, Y) in enumerate([(adjA, adjB), (adjB, adjA)]):
        for u in range(m):
            w4 = []; t2 = set()
            for v1, c1 in X[u]:
                for u2, c2 in Y[v1]:
                    if c2 == c1: continue
                    t2.add(u2)
                    for v3, c3 in X[u2]:
                        if c3 == c2: continue
                        for u4, c4 in Y[v3]:
                            if c4 == c3: continue
                            w4.append((u4, (c1, c2, c3, c4)))
            walks[side].append(w4); two[side].append(t2 - {u})
    for fp in flagfiles:
        sing = SING[fp]
        for pi in perms:
            cost = 0
            for side in range(2):
                S = sing[side]
                for u in range(m):
                    cov = set(two[side][u]); cov.add(u)
                    for u4, p in walks[side][u]:
                        if not S[code((pi[p[0]], pi[p[1]], pi[p[2]], pi[p[3]]))]: cov.add(u4)
                    cost += m - len(cov)
                if cost >= best[fp][0]: break
            if cost < best[fp][0]: best[fp] = (cost, (seed, pi))
    print('seed', seed, {fp.split('/')[-1]: best[fp][0] for fp in flagfiles}, flush=True)
for fp in flagfiles: print('BEST', fp, best[fp])
