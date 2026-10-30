#!/usr/bin/env python3
"""The (9,5) graph on 2,790 vertices as a Cayley graph (second description of d9D5_n2790_haar_c31c45.edges).

Group of order 2,790: G^ = <x, y, t | x^31 = y^45 = t^2 = 1, y x y^-1 = x^28, t x t = x^-1, t y = y t>
(= C31 : C90, with y t acting on <x> by 3 mod 31), elements x^i y^j t^e.  Connection set T = {s t : s in S},
S = {1, x^28 y^20, x^18 y^25, x^24 y^26, x^22 y^19, x^21 y^28, x^3 y^17, x^10 y^41, x^4 y^4}: one involution (t) and
four inverse pairs.  Edges g ~ g u for u in T.  Bipartite (e = 0 / e = 1), 9-regular; the script checks the
relations, that T = T^-1, the diameter by BFS from the identity (enough for a Cayley graph), and writes the edge list.
usage: build_d9D5_n2790_cayley.py OUT.edges
"""
import sys
from collections import deque
p, k, r = 31, 45, 28
rp = [pow(r, j, p) for j in range(k)]
gmul = lambda g, h: ((g[0] + rp[g[1]] * h[0]) % p, (g[1] + h[1]) % k)
beta = lambda g: ((-g[0]) % p, g[1])                      # conjugation by t: x -> x^-1, y -> y
def mul(a, b):
    (g, e), (h, d) = a, b
    return (gmul(g, beta(h) if e else h), (e + d) % 2)
S = [(0, 0), (28, 20), (18, 25), (24, 26), (22, 19), (21, 28), (3, 17), (10, 41), (4, 4)]
T = [(s, 1) for s in S]
els = [((i, j), e) for e in range(2) for i in range(p) for j in range(k)]
idx = {g: n for n, g in enumerate(els)}
one = ((0, 0), 0)
x, y, t = ((1, 0), 0), ((0, 1), 0), ((0, 0), 1)
def pw(g, n):
    a = one
    for _ in range(n): a = mul(a, g)
    return a
def inv(g):
    return next(h for h in els if mul(g, h) == one)
assert pw(x, 31) == one and pw(y, 45) == one and pw(t, 2) == one
assert mul(mul(y, x), inv(y)) == pw(x, 28) and mul(mul(t, x), t) == inv(x) and mul(t, y) == mul(y, t)
assert all(any(mul(u, v) == one for v in T) for u in T), "T must be inverse-closed"
assert len(set(T)) == 9
adj = [[idx[mul(g, u)] for u in T] for g in els]
dist = [-1] * len(els); dist[idx[one]] = 0; q = deque([idx[one]])
while q:
    a = q.popleft()
    for b in adj[a]:
        if dist[b] < 0: dist[b] = dist[a] + 1; q.append(b)
assert min(dist) >= 0, "disconnected"
print(f"vertices {len(els)} degree {len(T)} eccentricity of the identity {max(dist)} -> "
      f"{'VALID' if max(dist) == 5 else 'INVALID'} (Delta=9, D=5; Cayley graph, so the diameter is this eccentricity)")
with open(sys.argv[1], "w") as f:
    f.write(f"{len(els)}\n")
    for a in range(len(els)):
        for b in adj[a]:
            if a < b: f.write(f"{a} {b}\n")
