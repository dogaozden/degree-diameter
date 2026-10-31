import sys
exec(open('hexgraph.py').read().split('allpts = []')[0])
import random as R
R.seed(5)
def Lmat(x):
    cols = [cross(x, [int(i == j) for i in range(N)]) for j in range(N)]
    return [[cols[j][i] for j in range(N)] for i in range(N)]
def plane_pts(x):
    ns = nullspace(Lmat(x), N); dim = len(ns)
    pts = set()
    for cs in itertools.product(range(p), repeat=dim):
        if not any(cs): continue
        v = [sum(cs[k]*ns[k][i] for k in range(dim)) % p for i in range(N)]
        pts.add(norm(v))
    return frozenset(pts)
x = None
while x is None:
    v = tuple(R.randrange(p) for _ in range(N))
    if any(v) and Bq(v, v) == 0: x = norm(v)
Wx = plane_pts(x)
print("W_x size", len(Wx), "x in W_x", x in Wx)
same = 0; tot = 0
for y in list(Wx)[:10]:
    if y == x: continue
    Wy = plane_pts(y); tot += 1
    if Wy == Wx: same += 1
    print("W_y==W_x?", Wy == Wx, "|W_x cap W_y|", len(Wx & Wy))
print("same", same, "of", tot)
