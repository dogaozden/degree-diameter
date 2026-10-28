"""packing.py: large sets of pairwise disjoint perfect codes (spreads or ovoids) from a list (perfcodes enum output).
Randomized greedy + simple swaps; prints the best packing size found."""
import sys, numpy as np
codes = np.loadtxt(sys.argv[1], dtype=np.int64)
n = codes.max() + 1
M = np.zeros((len(codes), n), dtype=bool)
for i, c in enumerate(codes): M[i, c] = True
inter = (M.astype(np.int32) @ M.T.astype(np.int32)) > 0
disj = ~inter
rng = np.random.default_rng(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
best = []
for t in range(int(sys.argv[3]) if len(sys.argv) > 3 else 2000):
    order = rng.permutation(len(codes)); cand = np.ones(len(codes), dtype=bool); sol = []
    for i in order:
        if cand[i]:
            sol.append(i); cand &= disj[i]; cand[i] = False
    if len(sol) > len(best): best = sol; print('packing', len(best), flush=True)
print('best packing size', len(best), 'of', len(codes), 'codes; elements covered', len(best) * codes.shape[1], 'of', n)
np.savetxt(sys.argv[1] + '.pack', codes[best], fmt='%d')
