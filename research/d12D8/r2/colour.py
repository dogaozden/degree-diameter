"""Proper (q+1)-edge-colouring of the H(q) incidence graph by repeated perfect matchings (scipy Hopcroft-Karp).
Writes ../hex/col_q{q}_s{seed}.npy: int8 array (n, q+1), colour of edge (line l, its k-th point lines[l][k]).
usage: colour.py q seed"""
import sys, os, numpy as np
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import maximum_bipartite_matching
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
from hexlib import load_hex
q, seed = int(sys.argv[1]), int(sys.argv[2])
rng = np.random.default_rng(seed)
n, lines = load_hex(q)
col = -np.ones((n, q + 1), dtype=np.int8)
alive = np.ones((n, q + 1), dtype=bool)
for c in range(q + 1):
    perm = rng.permutation(n)            # random relabelling of points to vary the matching
    rows, cols = np.nonzero(alive)
    pts = perm[lines[rows, cols]]
    A = csr_matrix((np.ones(len(rows)), (rows, pts)), shape=(n, n))
    mt = maximum_bipartite_matching(A, perm_type='column')   # mt[l] = permuted point matched to line l
    assert (mt >= 0).all(), 'no perfect matching'
    for l in range(n):
        k = np.nonzero((perm[lines[l]] == mt[l]) & alive[l])[0][0]
        col[l, k] = c; alive[l, k] = False
assert (col >= 0).all()
# check proper at points
pc = {}
for l in range(n):
    for k in range(q + 1):
        key = (int(lines[l, k]), int(col[l, k])); assert key not in pc; pc[key] = l
out = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'hex', f'col_q{q}_s{seed}.npy')
np.save(out, col); print(out)
