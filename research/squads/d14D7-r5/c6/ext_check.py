"""c6 step 0: how far is R756 from extendable?  For every singular point x outside R, count the points of R
orthogonal to x (B(x,r) == 0).  0 would mean R756 + x is a valid 757-set.  Also the distribution of counts."""
import os, sys, time
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import *

t0 = time.time()
R = load_points(R756_PATH)
P = all_singular_points()
print('singular points', len(P), flush=True)
inR = key_set(R)
mask = np.array([tuple(int(v) for v in r) not in inR for r in P])
X = P[mask]
Bm = gram_B(X, R)
orth = (Bm == 0).sum(axis=1)
hist = np.bincount(orth)
print('outside points', len(X), 'time %.1fs' % (time.time() - t0))
print('histogram: number of R-points orthogonal to x -> count of x (first 12 values)')
for k in range(min(12, len(hist))):
    print(f'  {k}: {hist[k]}')
print('min orthogonal count', int(orth.min()))
cand = X[orth == 0]
print('extendable points (orthogonal to none of R):', len(cand))
np.save(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'ext_counts.npy'), orth)
if len(cand):
    write_points(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'ext757.txt'),
                 np.vstack([R, cand[:1]]), 'R756 plus one extension point')
