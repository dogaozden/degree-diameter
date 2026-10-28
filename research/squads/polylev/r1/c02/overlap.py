"""c02 overlap.py: all-pairs intersection sizes |S_v cap S_w| of the sampled Hermitian spreads (sparse
inverted-index method: for each line, every pair of spreads containing it gets +1), the histogram over pairs,
and the disjointness graph. Usage: python3 overlap.py SPREADS.npz OUT_PREFIX"""
import os, sys, time
os.environ.setdefault('OMP_NUM_THREADS', '1'); os.environ.setdefault('OPENBLAS_NUM_THREADS', '1')
import numpy as np
t0 = time.time()
d = np.load(sys.argv[1]); S = d['S']; V = d['V']
out = sys.argv[2]
M, w = S.shape
flat = S.ravel()
sid = np.repeat(np.arange(M, dtype=np.int32), w)
order = np.argsort(flat, kind='stable')
fs, ss = flat[order], sid[order]
bounds = np.flatnonzero(np.diff(fs)) + 1
C = np.zeros((M, M), dtype=np.int16)
for g in np.split(ss, bounds):
    if len(g) > 1:
        C[np.ix_(g, g)] += 1
print('M', M, 'line size', w, 'lines covered', len(bounds) + 1, 'secs', round(time.time() - t0, 1), flush=True)
assert (np.diag(C) == w).all()
hist = np.zeros(w + 1, dtype=np.int64)
for i in range(M - 1):
    hist += np.bincount(C[i, i + 1:], minlength=w + 1)[:w + 1]
pairs = M * (M - 1) // 2
nz = {int(k): int(v) for k, v in enumerate(hist) if v}
print('pairs', pairs, 'overlap histogram (overlap: count):', nz, flush=True)
mean = sum(k * v for k, v in nz.items()) / pairs
print('mean overlap', round(mean, 3))
# independent spot check of a few pairs with intersect1d
rng = np.random.default_rng(7)
bad = 0
for _ in range(300):
    i, j = rng.choice(M, 2, replace=False)
    if np.intersect1d(S[i], S[j]).size != C[i, j]:
        bad += 1
print('spot check mismatches (of 300):', bad)
D = C == 0
np.fill_diagonal(D, False)
deg = D.sum(1)
print('disjoint pairs', int(D.sum()) // 2, 'density', round(float(D.sum()) / (M * (M - 1)), 6),
      'max degree', int(deg.max()), 'mean degree', round(float(deg.mean()), 2), 'isolated', int((deg == 0).sum()))
np.save(out + '_overlap.npy', C)
np.save(out + '_disjoint_adj_rows.npy', np.packbits(D, axis=1))
print('secs', round(time.time() - t0, 1))
