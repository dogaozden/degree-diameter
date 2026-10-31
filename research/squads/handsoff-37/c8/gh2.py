# Build the incidence graph of GH(2,2) (split Cayley hexagon H(2)) as points of Q(6,2) and its 63 lines
# satisfying the Tits equations (checked computationally: 63 lines, 3 per point, girth 12, diameter 6).
import itertools, sys
from collections import deque
def Q(x):  # x0x4 + x1x5 + x2x6 + x3^2 over GF(2)
    return (x[0]*x[4] + x[1]*x[5] + x[2]*x[6] + x[3]) % 2   # x3^2 = x3 over GF(2)
vecs = [v for v in itertools.product([0,1], repeat=7) if any(v)]
pts = [v for v in vecs if Q(v) == 0]
assert len(pts) == 63, len(pts)
def add(u, v): return tuple((a+b) % 2 for a, b in zip(u, v))
def B(u, v): return (Q(add(u, v)) - Q(u) - Q(v)) % 2   # bilinear form (polarisation)
def plk(x, y):
    return {(i, j): (x[i]*y[j] + x[j]*y[i]) % 2 for i in range(7) for j in range(i+1, 7)}
lines = set()
for x, y in itertools.combinations(pts, 2):
    if B(x, y) == 0:
        L = frozenset([x, y, add(x, y)])
        if all(p in set(pts) for p in L): lines.add(L)
print("totally singular lines of Q(6,2):", len(lines), file=sys.stderr)
def tits(L):
    x, y = sorted(L)[:2]
    p = plk(x, y)
    # p_ij indices are 0-based here: p12->(1,2), p34->(3,4), p54->(4,5), p32->(2,3), p20->(0,2), p35->(3,5),
    # p65->(5,6), p30->(0,3), p01->(0,1), p36->(3,6), p46->(4,6), p31->(1,3)
    eqs = [((1,2),(3,4)), ((4,5),(2,3)), ((0,2),(3,5)), ((5,6),(0,3)), ((0,1),(3,6)), ((4,6),(1,3))]
    return all(p[a] == p[b] for a, b in eqs)
H = [L for L in lines if tits(L)]
print("lines satisfying Tits equations:", len(H), file=sys.stderr)
pts_idx = {p: i for i, p in enumerate(pts)}
Hl = list(H)
edges = []
for li, L in enumerate(Hl):
    for p in L: edges.append((pts_idx[p], 63 + li))
deg = [0]*126
for a, b in edges: deg[a] += 1; deg[b] += 1
print("degrees:", sorted(set(deg)), file=sys.stderr)
if len(Hl) == 63 and set(deg) == {3}:
    with open(sys.argv[1], 'w') as f:
        f.write("126\n")
        for a, b in edges: f.write(f"{a} {b}\n")
    print("wrote", sys.argv[1], file=sys.stderr)
