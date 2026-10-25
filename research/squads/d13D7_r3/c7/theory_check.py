import sys, numpy as np, itertools
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d13D7_r3/c7')
from common import *
coord, code = load_hex()
N = len(coord)
D = directions()
print('directions', len(D))
# S0 = points at infinity (x0=0, x!=e4) with x5 = 2 x1
e4 = np.array([0,0,0,0,1,0,0])
inf = coord[coord[:,0] == 0]
S0 = [x for x in inf if not np.array_equal(x, e4) and (x[5] - 2 * x[1]) % Q == 0]
print('points at infinity with x5=2x1 (excluding e4):', len(S0))
# check formula: every S0 point equals dir_point(n,z) for its direction
def direction_of(x):
    n = normalize(np.array([x[1], x[6], (-2 * x[3]) % Q, x[2]]))
    return tuple(n)
Dset = {tuple(d): i for i, d in enumerate(D)}
dirs_S0 = [direction_of(x) for x in S0]
print('all S0 directions on E:', all(d in Dset for d in dirs_S0), 'distinct directions:', len(set(dirs_S0)))
# opposition among S0 vs direction: B != 0 iff directions differ (sample all pairs)
S = np.array(S0)
Bm = (np.einsum('i,j->ij', S[:,1], S[:,5]) + np.einsum('i,j->ij', S[:,5], S[:,1])
      + np.einsum('i,j->ij', S[:,2], S[:,6]) + np.einsum('i,j->ij', S[:,6], S[:,2])
      - 2 * np.einsum('i,j->ij', S[:,3], S[:,3])) % Q
dd = np.array([[Dset[d] for d in dirs_S0]])[0]
same = dd[:, None] == dd[None, :]
np.fill_diagonal(same, True)
print('B==0 pairs equal same-direction pairs:', np.array_equal(Bm == 0, same))
# check B on the full hexagon formula for dir_point
x = dir_point(D[5], 3)
print('dir_point on hexagon:', point_index(code, x) >= 0)
