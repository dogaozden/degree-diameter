# Build the incidence graph of W(3) (GQ(3,3)): 40 points, 40 totally isotropic lines of the symplectic form on GF(3)^4.
import itertools, sys
q = 3
def norm(v):
    for x in v:
        if x % q:
            inv = 1 if x % q == 1 else 2
            return tuple((y * inv) % q for y in v)
    return None
pts = sorted({norm(v) for v in itertools.product(range(q), repeat=4) if any(v)})
assert len(pts) == 40
def B(x, y):  # symplectic form
    return (x[0]*y[1] - x[1]*y[0] + x[2]*y[3] - x[3]*y[2]) % q
lines = set()
for p, r in itertools.combinations(pts, 2):
    if B(p, r) == 0:
        span = set()
        for a, b in itertools.product(range(q), repeat=2):
            v = tuple((a*p[i] + b*r[i]) % q for i in range(4))
            if any(v):
                span.add(norm(v))
        lines.add(frozenset(span))
lines = sorted(lines, key=lambda s: sorted(s))
assert len(lines) == 40 and all(len(L) == 4 for L in lines)
idx = {p: i for i, p in enumerate(pts)}
edges = []
for j, L in enumerate(lines):
    for p in L:
        edges.append((idx[p], 40 + j))
deg = [0]*80
for u, v in edges: deg[u] += 1; deg[v] += 1
assert all(d == 4 for d in deg)
with open('/home/user/degree-diameter/research/squads/b48/r1/c24/w3.txt', 'w') as f:
    f.write(f"80 {len(edges)}\n")
    for u, v in edges: f.write(f"{u} {v}\n")
print("ok", len(edges))
