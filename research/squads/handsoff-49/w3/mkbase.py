# Build W(3) incidence graph: points of PG(3,3), totally isotropic lines of the symplectic form.
import itertools, sys
from itertools import product
def B(x, y):
    return (x[0]*y[1] - x[1]*y[0] + x[2]*y[3] - x[3]*y[2]) % 3
pts = []
for v in product(range(3), repeat=4):
    if any(v):
        # normalize: first nonzero coordinate = 1
        i = next(k for k in range(4) if v[k])
        if v[i] == 1:
            pts.append(v)
pts = sorted(set(pts))
assert len(pts) == 40, len(pts)
def span(a, b):
    s = set()
    for c1, c2 in product(range(3), repeat=2):
        w = tuple((c1*a[k] + c2*b[k]) % 3 for k in range(4))
        if any(w):
            i = next(k for k in range(4) if w[k])
            if w[i] == 1:
                s.add(w)
    return frozenset(s)
lines = set()
for a, b in itertools.combinations(pts, 2):
    if B(a, b) == 0:
        lines.add(span(a, b))
lines = sorted(lines, key=lambda L: sorted(L))
assert len(lines) == 40, len(lines)
pidx = {p: i for i, p in enumerate(pts)}
edges = []
for li, L in enumerate(lines):
    assert len(L) == 4
    for p in L:
        edges.append((pidx[p], 40 + li))
out = sys.argv[1]
with open(out, 'w') as f:
    f.write("80 %d\n" % len(edges))
    for u, v in edges:
        f.write("%d %d\n" % (u, v))
print("edges", len(edges))
