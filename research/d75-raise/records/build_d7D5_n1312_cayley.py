#!/usr/bin/env python3
"""The (7,5) graph on 1,312 vertices as a Cayley graph (second, independent description of
d7D5_n1312_haar_c41c16.edges; nauty: same canonical form).

Group of order 1,312: Ĝ = <x, y, t | x^41 = y^16 = t^2 = 1, y x y^-1 = x^38, t x t = x^-1, t y t = y^9>,
elements (x^i y^j, e) = x^i y^j t^e.  Connection set T = {s t : s in S}, S = {1, x^3 y^8, x^18 y^8, x^14 y^3,
x y^5, x^32 y^14, x y^2}: three involutions (the first three) and two inverse pairs.  Edges g ~ g u for u in T.
The graph is bipartite (e = 0 / e = 1), 7-regular; this script checks the diameter by BFS from the identity
(enough for a Cayley graph) and writes the edge list.   usage: build_d7D5_n1312_cayley.py OUT.edges
"""
import sys
from collections import deque
p, k, r = 41, 16, 38
rp = [pow(r, j, p) for j in range(k)]
gmul = lambda g, h: ((g[0] + rp[g[1]] * h[0]) % p, (g[1] + h[1]) % k)
beta = lambda g: ((-g[0]) % p, (9 * g[1]) % k)          # conjugation by t: x -> x^-1, y -> y^9
def mul(a, b):
    (g, e), (h, d) = a, b
    return (gmul(g, beta(h) if e else h), (e + d) % 2)
S = [(0, 0), (3, 8), (18, 8), (14, 3), (1, 5), (32, 14), (1, 2)]
T = [(s, 1) for s in S]
els = [((i, j), e) for e in range(2) for i in range(p) for j in range(k)]
idx = {g: n for n, g in enumerate(els)}
one = ((0, 0), 0)
assert all(any(mul(u, v) == one for v in T) for u in T), "T must be inverse-closed"
# relations of the presentation
x, y, t = ((1, 0), 0), ((0, 1), 0), ((0, 0), 1)
def pw(g, n):
    a = one
    for _ in range(n): a = mul(a, g)
    return a
inv = lambda g: next(h for h in els if mul(g, h) == one)
assert pw(x, 41) == one and pw(y, 16) == one and pw(t, 2) == one
assert mul(mul(y, x), inv(y)) == pw(x, 38) and mul(mul(t, x), t) == inv(x) and mul(mul(t, y), t) == pw(y, 9)
adj = [[idx[mul(g, u)] for u in T] for g in els]
dist = [-1] * len(els); dist[idx[one]] = 0; q = deque([idx[one]])
while q:
    a = q.popleft()
    for b in adj[a]:
        if dist[b] < 0: dist[b] = dist[a] + 1; q.append(b)
edges = sorted({(min(a, b), max(a, b)) for a in range(len(els)) for b in adj[a]})
with open(sys.argv[1], "w") as f:
    f.write(f"{len(els)}\n")
    for a, b in edges: f.write(f"{a} {b}\n")
print(f"vertices {len(els)} edges {len(edges)} eccentricity of the identity {max(dist)} "
      f"(Cayley graph: diameter = eccentricity) -> {'VALID' if max(dist) == 5 and min(dist) >= 0 else 'INVALID'}")
