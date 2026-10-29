import sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/conics2-r1/tools')
import numpy as np
from hexload import load
from transcheck import bad_pairs
q, N, LP, PL, X = load('/home/user/degree-diameter/research/squads/conics2-r1/data/hex_q5.bin')
A = np.zeros((N, N), np.float32)           # A[p, l] = 1 if p on l
for l in range(N):
    A[LP[l], l] = 1
P2 = (A @ A.T) > 0.5                        # collinear points (incl diagonal)
np.fill_diagonal(P2, False)
LL = (A.T @ A) > 0.5                        # lines meeting (incl diagonal)
np.fill_diagonal(LL, False)
print('deg points', P2.sum(1)[:3], 'deg lines', LL.sum(1)[:3])
lines = open('/home/user/degree-diameter/research/frontier/sols/d7D7_hex5_mirror81_n23598.sol').read().split('\n')
R = np.array([int(t) for t in lines[1].split()[1:]])
sig = np.array([int(t) for s in lines[3:] for t in s.split()], dtype=np.int64)
print('|R|', len(R), 'sigma bijection', len(np.unique(sig)) == N)
def good_mask(sig):
    LLs = LL[np.ix_(sig, sig)]            # LLs[x,y] = lines sig[x], sig[y] meet
    viol = (P2 & ~LLs).sum(1)
    return viol == 0
g = good_mask(sig)
print('good points under record sigma:', g.sum(), ' R subset of good:', g[R].all())
# collinearity inside R
Rc = P2[np.ix_(R, R)].sum() // 2
print('collinear pairs inside R:', Rc)
# sigma(R) concurrency: count lines of sigma(R) through common point
from collections import Counter
cnt = Counter(p for l in sig[R] for p in LP[l])
print('max #sigma(R) lines through a point', max(cnt.values()))
print('transcheck bad pairs on good set:', bad_pairs(q, N, LP, PL, sig, np.nonzero(g)[0]))
print('transcheck bad pairs on record R:', bad_pairs(q, N, LP, PL, sig, R))
np.save('/home/user/degree-diameter/research/squads/conics2-r1/c2/A.npy', A)
