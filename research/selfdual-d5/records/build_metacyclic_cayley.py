#!/usr/bin/env python3
"""build_metacyclic_cayley.py m k r u t v "i,j ..." OUT.edges [D]: the Haar graph H(G,S) of
G = <x, y | x^m = y^k = 1, y x y^-1 = x^r> with a self-dual S, written as a Cayley graph of G^ = G : <tau>,
tau g tau = beta(g), beta(x) = x^u, beta(y) = x^t y^v (an involutory automorphism with beta(s)^-1 in S for s in S).
Elements (g, e) = g tau^e; connection set T = {(s, 1) : s in S}; edges a ~ a u (u in T).  Checks the relations, that
beta is an involution, that T = T^-1, and the diameter by BFS from the identity (enough for a Cayley graph)."""
import sys
from collections import deque
m, k, r, u, t, v = (int(a) for a in sys.argv[1:7])
S = [tuple(int(z) for z in p.split(",")) for p in sys.argv[7].split()]
out = sys.argv[8]; D = int(sys.argv[9]) if len(sys.argv) > 9 else 5
rp = [pow(r, j, m) for j in range(k)]
gmul = lambda g, h: ((g[0] + rp[g[1]] * h[0]) % m, (g[1] + h[1]) % k)
def gpw(g, e):
    a = (0, 0)
    for _ in range(e): a = gmul(a, g)
    return a
bx, by = (u % m, 0), (t % m, v % k)
bcache = {}
def beta(g):
    if g not in bcache: bcache[g] = gmul(gpw(bx, g[0]), gpw(by, g[1]))
    return bcache[g]
def mul(a, b):
    (g, e), (h, d) = a, b
    return (gmul(g, beta(h) if e else h), (e + d) % 2)
one = ((0, 0), 0)
G = [(i, j) for i in range(m) for j in range(k)]
assert all(beta(beta(g)) == g for g in G), "beta must be an involution"
assert all(beta(gmul(g, h)) == gmul(beta(g), beta(h)) for g in [(1, 0), (0, 1)] for h in G), "beta must be a homomorphism"
els = [(g, e) for e in range(2) for g in G]
idx = {a: n for n, a in enumerate(els)}
T = [(s, 1) for s in S]
assert len(set(T)) == len(T) and all(any(mul(a, b) == one for b in T) for a in T), "T must be inverse-closed"
adj = [[idx[mul(a, b)] for b in T] for a in els]
dist = [-1] * len(els); dist[idx[one]] = 0; q = deque([idx[one]])
while q:
    a = q.popleft()
    for b in adj[a]:
        if dist[b] < 0: dist[b] = dist[a] + 1; q.append(b)
assert min(dist) >= 0, "disconnected"
ecc = max(dist)
print(f"vertices {len(els)} degree {len(T)} eccentricity of the identity {ecc} -> "
      f"{'VALID' if ecc == D else 'INVALID'} (Delta={len(T)}, D={D}; Cayley graph, so the diameter is this eccentricity)")
with open(out, "w") as f:
    f.write(f"{len(els)}\n")
    for a in range(len(els)):
        for b in adj[a]:
            if a < b: f.write(f"{a} {b}\n")
