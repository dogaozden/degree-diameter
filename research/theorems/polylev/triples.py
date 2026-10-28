"""triples.py: is there a set of three pairwise disjoint codes in a list (perfcodes enum output)? Exact: for each
code i, look for a disjoint pair among the codes disjoint from i."""
import sys
import numpy as np
codes = np.loadtxt(sys.argv[1], dtype=np.int64)
n = codes.max() + 1
M = np.zeros((len(codes), n), dtype=np.float32)
for i, c in enumerate(codes):
    M[i, c] = 1
disj = (M @ M.T) == 0
np.fill_diagonal(disj, False)
print('codes:', len(codes), 'disjoint pairs:', int(disj.sum()) // 2, flush=True)
found = False
for i in range(len(codes)):
    D = np.where(disj[i])[0]
    if disj[np.ix_(D, D)].any():
        found = True
        print('triple found with code', i)
        break
print('three pairwise disjoint codes exist:', found)
