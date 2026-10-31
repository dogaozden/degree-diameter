import sys
sys.argv = ['x']
exec(open('hexgraph.py').read().split('allpts = []')[0])
import random as R
R.seed(3)
def Lmat(x):
    cols = [cross(x, [int(i == j) for i in range(N)]) for j in range(N)]
    return [[cols[j][i] for j in range(N)] for i in range(N)]
def sing_pts_in_kernel(x):
    ns = nullspace(Lmat(x), N)
    dim = len(ns)
    # enumerate projective points in span
    pts = set()
    for cs in itertools.product(range(p), repeat=dim):
        if not any(cs): continue
        v = [sum(cs[k]*ns[k][i] for k in range(dim)) % p for i in range(N)]
        nv = norm(v)
        pts.add(nv)
    return dim, len(pts), sum(1 for q in pts if Bq(q, q) == 0)
for t in range(3):
    while True:
        v = tuple(R.randrange(p) for _ in range(N))
        if any(v) and Bq(v, v) == 0: break
    print(sing_pts_in_kernel(v))
