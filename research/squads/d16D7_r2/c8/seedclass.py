import numpy as np, sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d16D7_r2/c8')
from load import *
q, N, L, LP, X = load_hex()
M, E, rep_p, nb_p = load_og(D+'og_pts.txt')
M2, E2, rep_l, nb_l = load_og(D+'og_lines.txt')
a = X[:, 3]; v = X[:, 0:3]; w = X[:, 4:7]
c0 = (a[LP] == 0).sum(axis=1)
def read_sol(fn):
    return [int(x) for x in open(fn).read().split() if x.strip() and not x.startswith('#')]
sp = read_sol(D+'seed_pts.txt'); sl = read_sol(D+'seed_lines.txt')
print('seed pts', len(sp), 'seed lines', len(sl))
ap = np.array([a[rep_p[i]] == 0 for i in sp]); print('seed pts in a=0 hyperplane:', ap.sum(), 'of', len(sp))
vz = np.array([(v[rep_p[i]] == 0).all() for i in sp]); wz = np.array([(w[rep_p[i]] == 0).all() for i in sp])
print('seed pts with v=0', vz.sum(), 'w=0', wz.sum())
print('seed lines by #a0 points:', np.unique([c0[rep_l[i]] for i in sl], return_counts=True))
# how many all-vertex classes
M_p_a0 = np.array([a[rep_p[i]] == 0 for i in range(M)])
M_l_14 = np.array([c0[rep_l[i]] == 14 for i in range(M2)])
print('point vertices in a0:', M_p_a0.sum(), ' line vertices inside hyperplane:', M_l_14.sum())
# neighbour count of seed in a0 and affine
print('seed lines inside:', M_l_14[sl].sum())
