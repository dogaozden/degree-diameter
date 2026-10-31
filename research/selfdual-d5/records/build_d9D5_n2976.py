#!/usr/bin/env python3
"""The (9,5) graph on 2,976 vertices from its formula alone (no GAP): Haar graph H(G,S) of
G = C31 : (C3 x Q16) = SmallGroup(1488,11), elements (i,c,k,l) = x^i z^c a^k b^l, i mod 31, c mod 3, k mod 8, l mod 2,
with x of order 31, z of order 3 central in the complement, Q16 = <a, b | a^8 = 1, b^2 = a^4, b a b^-1 = a^-1>,
z x z^-1 = x^25, a x a^-1 = x, b x b^-1 = x^-1, so the product is
  (i,c,k,l)(i',c',k',l') = (i + 25^c (-1)^l i', c+c', k + (-1)^l k' + 4 [l = l' = 1], l+l').
S = {(0,0,0,0), (25,0,2,0), (18,0,6,0), (12,2,1,1), (10,1,7,1), (0,1,1,0), (0,2,5,0), (24,2,0,0), (11,1,0,0)};
(g,A) ~ (s g, B).  Vertex numbers: g = (i,c,k,l) -> i*48 + c*16 + k*2 + l on side A, plus 1488 on side B.
Self-dual: beta with x -> x^-1, z -> z, a -> a^3, b -> b is an involutory automorphism with beta(s)^-1 in S for s in S,
so the graph is also the Cayley graph of G : <tau> (tau g tau = beta(g)) with T = S tau; built here too.
usage: build_d9D5_n2976.py HAAR.edges [CAYLEY.edges]   (BFS from every vertex for the Haar graph)
"""
import sys
from collections import deque
from itertools import product
def mul(x, y):
    i, c, k, l = x; i2, c2, k2, l2 = y
    s = k + (-1) ** l * k2 + (4 if l == 1 and l2 == 1 else 0)
    return ((i + pow(25, c, 31) * (-1) ** l * i2) % 31, (c + c2) % 3, s % 8, (l + l2) % 2)
G = list(product(range(31), range(3), range(8), range(2)))
n = len(G); idx = {g: g[0]*48 + g[1]*16 + g[2]*2 + g[3] for g in G}
e = (0, 0, 0, 0)
S = [(0,0,0,0), (25,0,2,0), (18,0,6,0), (12,2,1,1), (10,1,7,1), (0,1,1,0), (0,2,5,0), (24,2,0,0), (11,1,0,0)]
adj = [[] for _ in range(2 * n)]; edges = []
for g in G:
    for s in S:
        a, b = idx[g], n + idx[mul(s, g)]; edges.append((a, b)); adj[a].append(b); adj[b].append(a)
assert all(len(set(x)) == len(x) == 9 for x in adj), "not simple 9-regular"
diam = 0
for s0 in range(2 * n):
    dist = [-1] * (2 * n); dist[s0] = 0; q = deque([s0])
    while q:
        u = q.popleft()
        for w in adj[u]:
            if dist[w] < 0: dist[w] = dist[u] + 1; q.append(w)
    assert min(dist) >= 0, "disconnected"
    diam = max(diam, max(dist))
print(f"Haar: vertices {2*n} edges {len(edges)} diameter {diam} -> {'VALID' if diam == 5 else 'INVALID'} (Delta=9, D=5)")
with open(sys.argv[1], "w") as f:
    f.write(f"{2 * n}\n")
    for a, b in edges: f.write(f"{a} {b}\n")
if len(sys.argv) > 2:
    gens = {(1,0,0,0): (30,0,0,0), (0,1,0,0): (0,1,0,0), (0,0,1,0): (0,0,3,0), (0,0,0,1): (0,0,0,1)}
    beta = {e: e}; q = deque([e])                       # extend beta from the generators along a BFS
    while q:
        g = q.popleft()
        for s, bs in gens.items():
            h = mul(g, s)
            if h not in beta: beta[h] = mul(beta[g], bs); q.append(h)
    assert len(beta) == n and all(beta[mul(x, y)] == mul(beta[x], beta[y]) for x in G for y in G), "beta not an automorphism"
    assert all(beta[beta[x]] == x for x in G), "beta not an involution"
    inv = {}
    for g in G:
        for h in G:
            if mul(g, h) == e: inv[g] = h; break
    assert {inv[beta[s]] for s in S} == set(S), "S not self-dual"
    M = lambda a, b: (mul(a[0], beta[b[0]] if a[1] else b[0]), (a[1] + b[1]) % 2)
    els = [(g, t) for t in range(2) for g in G]; eid = {x: k for k, x in enumerate(els)}
    T = [(s, 1) for s in S]
    assert all(any(M(u, v) == (e, 0) for v in T) for u in T), "T not inverse-closed"
    cadj = [[eid[M(x, u)] for u in T] for x in els]
    dist = [-1] * len(els); dist[eid[(e, 0)]] = 0; q = deque([eid[(e, 0)]])
    while q:
        u = q.popleft()
        for w in cadj[u]:
            if dist[w] < 0: dist[w] = dist[u] + 1; q.append(w)
    print(f"Cayley: vertices {len(els)} eccentricity of the identity {max(dist)} -> {'VALID' if min(dist) >= 0 and max(dist) == 5 else 'INVALID'}")
    with open(sys.argv[2], "w") as f:
        f.write(f"{len(els)}\n")
        for a in range(len(els)):
            for b in cadj[a]:
                if a < b: f.write(f"{a} {b}\n")
