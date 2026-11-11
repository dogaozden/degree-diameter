"""Independent edge list of the bi-coset graph of G = Z_m x|_r Z_k with H = <(0,k/h)> (order h).
Vertices: right cosets xH on side A (ids 0..N-1) and side B (ids N..2N-1); A-coset xH ~ B-coset (x s)H for s in N0.
Well-definedness across representatives of xH is asserted.  Usage: mkedges.py m kp h r OUT u1 v1 u2 v2 u3 v3 u4 v4"""
import sys
m, kp, h, r = map(int, sys.argv[1:5]); out = sys.argv[5]
pairs = [(int(sys.argv[6 + 2 * i]), int(sys.argv[7 + 2 * i])) for i in range(4)]
k = h * kp
assert pow(r, k, m) == 1 % m
zeta = pow(r, kp, m)
for (u, v) in pairs: assert (zeta * u) % m in [uu for uu, vv in pairs if vv == v], "N0 not zeta-invariant"
def mul(x, y):
    a, j = x; b, l = y
    return ((a + pow(r, j, m) * b) % m, (j + l) % k)
G = [(a, j) for a in range(m) for j in range(k)]
Hs = [(0, kp * t % k) for t in range(h)]
def coset(x): return frozenset(mul(x, hh) for hh in Hs)
cos = sorted({coset(x) for x in G}, key=lambda c: sorted(c))
N = len(cos); cid = {}
for i, c in enumerate(cos):
    for x in c: cid[x] = i
edges = set()
for i, c in enumerate(cos):
    nbs = None
    for x in c:
        cur = frozenset(cid[mul(x, s)] for s in pairs)
        if nbs is None: nbs = cur
        assert cur == nbs, "neighbourhood depends on representative"
    assert len(nbs) == 4, "degree %d" % len(nbs)
    for b in nbs: edges.add((i, N + b))
with open(out, 'w') as f:
    f.write("%d\n" % (2 * N))
    for a, b in sorted(edges): f.write("%d %d\n" % (a, b))
deg = [0] * (2 * N)
for a, b in edges: deg[a] += 1; deg[b] += 1
print("N", N, "vertices", 2 * N, "edges", len(edges), "degrees", set(deg))
