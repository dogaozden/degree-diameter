#!/usr/bin/env python3
"""The (9,5) graph on 2,970 vertices from its formula alone (no GAP): Haar graph H(G,S) of
G = Heis(3) x (C11 : C5) = SmallGroup(1485,4), elements (a,b,c,i,j), a,b,c mod 3, i mod 11, j mod 5, product
  (a,b,c,i,j)(a',b',c',i',j') = (a+a', b+b', c+c'+a b', i + 3^j i', j+j')
(the Heisenberg group of upper unitriangular 3x3 matrices [[1,a,c],[0,1,b],[0,0,1]] mod 3, times C11 : C5 with
y x y^-1 = x^3).  S = {(0,0,0,0,0), (1,2,0,5,0), (0,0,1,2,0), (2,1,1,9,4), (2,1,1,3,1), (1,0,2,10,1), (2,0,2,4,4),
(1,1,1,5,1), (0,1,2,6,4)}; (g,A) ~ (s g, B).  Vertex numbers: g = (a,b,c,i,j) -> a*495 + b*165 + c*55 + i*5 + j on side
A, plus 1485 on side B.
Self-dual: beta, the automorphism with beta(1,0,0,0,0) = (1,0,0,0,0), beta(0,1,0,0,0) = (2,2,2,0,0),
beta(0,0,0,1,0) = (0,0,0,10,0), beta(0,0,0,0,1) = (0,0,0,9,1), is an involution with beta(s)^-1 in S for s in S, so the
graph is also the Cayley graph of G : <tau> (tau g tau = beta(g)) with T = S tau; built here too.
usage: build_d9D5_n2970.py HAAR.edges [CAYLEY.edges]   (BFS from every vertex for the Haar graph)
"""
import sys
from collections import deque
from itertools import product
mul = lambda x, y: ((x[0]+y[0]) % 3, (x[1]+y[1]) % 3, (x[2]+y[2]+x[0]*y[1]) % 3, (x[3] + pow(3, x[4], 11)*y[3]) % 11, (x[4]+y[4]) % 5)
G = list(product(range(3), range(3), range(3), range(11), range(5)))
n = len(G); idx = {g: a*495 + b*165 + c*55 + i*5 + j for g in G for (a, b, c, i, j) in [g]}
e = (0, 0, 0, 0, 0)
S = [(0,0,0,0,0), (1,2,0,5,0), (0,0,1,2,0), (2,1,1,9,4), (2,1,1,3,1), (1,0,2,10,1), (2,0,2,4,4), (1,1,1,5,1), (0,1,2,6,4)]
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
    gens = {(1,0,0,0,0): (1,0,0,0,0), (0,1,0,0,0): (2,2,2,0,0), (0,0,0,1,0): (0,0,0,10,0), (0,0,0,0,1): (0,0,0,9,1)}
    beta = {e: e}; q = deque([e])                       # extend beta from the generators along a BFS
    while q:
        g = q.popleft()
        for s, bs in gens.items():
            h = mul(g, s)
            if h not in beta: beta[h] = mul(beta[g], bs); q.append(h)
    assert len(beta) == n and all(beta[mul(x, y)] == mul(beta[x], beta[y]) for x in G for y in G), "beta not an automorphism"
    assert all(beta[beta[x]] == x for x in G), "beta not an involution"
    inv = {g: h for g in G for h in [next(h for h in G if mul(g, h) == e)]} if False else None
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
