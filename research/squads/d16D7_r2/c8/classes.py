import numpy as np, sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d16D7_r2/c8')
from load import *
q, N, L, LP, X = load_hex()
M, E, rep_p, nb_p = load_og(D+'og_pts.txt')
M2, E2, rep_l, nb_l = load_og(D+'og_lines.txt')
a = X[:, 3]; v = X[:, 0:3]; w = X[:, 4:7]
a0 = (a == 0)
print('points with a=0:', a0.sum(), 'orbits-of-a0 count', a0.sum()/61)
# lines: number of a=0 points
c0 = a0[LP].sum(axis=1)
print('lines by #a0 points:', np.unique(c0, return_counts=True))
# point-orbit classes among vertices
vp = rep_p
cls = {}
va0 = (v == 0).all(axis=1); wa0 = (w == 0).all(axis=1)
print('vertices a=0:', a0[vp].sum(), ' v=0:', va0[vp].sum(), ' w=0:', wa0[vp].sum())
print('vertices a!=0:', (~a0[vp]).sum())
# lines through a=0 structure: lines fully in a=0 hyperplane
inH = (c0 == 14)
print('lines inside a=0 hyperplane:', inH.sum())
# lines of vertices by c0
print('line vertices by c0:', np.unique(c0[rep_l], return_counts=True))
# points: count H-lines through point p that are inside hyperplane
cnt_in = np.bincount(LP[inH].ravel(), minlength=N)
print('a=0 points: #hex lines inside hyperplane through them:', np.unique(cnt_in[a0], return_counts=True))
print('non-a0 points: #hex lines inside hyperplane:', np.unique(cnt_in[~a0], return_counts=True))
