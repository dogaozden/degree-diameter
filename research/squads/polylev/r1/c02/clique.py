"""c02 clique.py: largest family of pairwise disjoint Hermitian spreads = maximum clique of the disjointness graph
D (D[i,j] iff |S_i cap S_j| = 0). Randomized greedy restarts, then exact branch and bound (networkx
max_weight_clique) on the sparse disjointness graph within a time limit.
Usage: python3 clique.py SPREADS.npz OVERLAP.npy RESTARTS SECONDS OUT.json"""
import os, sys, time, json
os.environ.setdefault('OMP_NUM_THREADS', '1'); os.environ.setdefault('OPENBLAS_NUM_THREADS', '1')
import numpy as np
import networkx as nx
t0 = time.time()
S = np.load(sys.argv[1])['S']
C = np.load(sys.argv[2])
restarts, secs, out = int(sys.argv[3]), float(sys.argv[4]), sys.argv[5]
M = len(S)
D = C == 0
np.fill_diagonal(D, False)
rng = np.random.default_rng(12345)
best = []
sizes = {}
for r in range(restarts):
    cand = np.ones(M, dtype=bool)
    sol = []
    while cand.any():
        idx = np.flatnonzero(cand)
        v = int(idx[rng.integers(len(idx))])
        sol.append(v)
        cand &= D[v]
        cand[v] = False
    sizes[len(sol)] = sizes.get(len(sol), 0) + 1
    if len(sol) > len(best):
        best = sol
        print('greedy restart', r, 'family size', len(best), flush=True)
print('greedy size histogram:', dict(sorted(sizes.items())), 'secs', round(time.time() - t0, 1), flush=True)
# exact search on the disjointness graph (sparse: list edges)
iu = np.argwhere(np.triu(D, 1))
G = nx.Graph()
G.add_nodes_from(range(M))
G.add_edges_from(map(tuple, iu.tolist()))
print('disjointness graph: nodes', G.number_of_nodes(), 'edges', G.number_of_edges(), flush=True)
exact = False
cl = None
try:
    # maximal cliques are enumerated lazily; keep the largest one (bounded by time)
    biggest = []
    n_max = 0
    for c in nx.find_cliques(G):
        n_max += 1
        if len(c) > len(biggest):
            biggest = c
            print('maximal clique size', len(c), 'after', n_max, 'cliques', round(time.time() - t0, 1), flush=True)
        if time.time() - t0 > secs:
            break
    else:
        exact = True
    if len(biggest) > len(best):
        best = biggest
    print('maximal cliques enumerated', n_max, 'complete', exact, flush=True)
except Exception as e:
    print('clique enumeration failed:', e, flush=True)
fam = sorted(int(x) for x in best)
# independent check: pairwise disjointness via sorted-array intersections
ok = all(np.intersect1d(S[a], S[b]).size == 0 for ia, a in enumerate(fam) for b in fam[ia + 1:])
res = {'family_size': len(fam), 'family_ids': fam, 'pairwise_disjoint_checked': bool(ok),
       'exact_enumeration_complete': exact, 'secs': round(time.time() - t0, 1)}
json.dump(res, open(out, 'w'))
print('family size', len(fam), 'pairwise disjoint (independent check):', ok, 'exact:', exact)
