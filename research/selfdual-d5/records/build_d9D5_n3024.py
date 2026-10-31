#!/usr/bin/env python3
"""The (9,5) graph on 3,024 vertices from its formula alone (no GAP): Haar graph H(G,S) of
G = C7 : (C3 x ((C3 x C3) : C8)) = SmallGroup(1512,783), elements (i,c,a,b,k) = x^i z^c w1^a w2^b u^k with x of order
7, z of order 3 (central in the complement), w = (a,b) in F3^2, u of order 8 acting on F3^2 by M = [[2,2],[1,2]]
(mod 3, columns = images of w1, w2), z x z^-1 = x^2, u x u^-1 = x^-1, w x w^-1 = x; product
  (i,c,a,b,k)(i',c',a',b',k') = (i + 2^c (-1)^k i', c+c', (a,b) + M^k (a',b'), k+k').
S = {(0,0,0,0,0), (5,0,1,0,0), (2,0,0,2,2), (0,2,0,1,4), (0,1,2,1,4), (0,2,1,2,3), (0,1,0,1,7), (5,2,1,2,0),
(3,1,1,1,0)}; (g,A) ~ (s g, B).  Vertex numbers: g = (i,c,a,b,k) -> i*216 + c*72 + a*24 + b*8 + k on side A, plus 1512
on side B.
Self-dual: beta with x -> x^-1, z -> z, w1 -> w1^2, w2 -> w2, u -> w1^2 w2 u^3 is an involutory automorphism with
beta(s)^-1 in S for s in S, so the graph is also the Cayley graph of G : <tau> (tau g tau = beta(g)) with T = S tau.
usage: build_d9D5_n3024.py HAAR.edges [CAYLEY.edges]   (BFS from every vertex for the Haar graph)
"""
import sys
from collections import deque
from itertools import product
M = [[2, 2], [1, 2]]
def mpow(k):
    R = [[1, 0], [0, 1]]
    for _ in range(k): R = [[sum(R[r][q] * M[q][c] for q in range(2)) % 3 for c in range(2)] for r in range(2)]
    return R
MP = [mpow(k) for k in range(8)]
def mul(x, y):
    i, c, a, b, k = x; i2, c2, a2, b2, k2 = y
    R = MP[k]
    return ((i + pow(2, c, 7) * (-1) ** k * i2) % 7, (c + c2) % 3, (a + R[0][0] * a2 + R[0][1] * b2) % 3,
            (b + R[1][0] * a2 + R[1][1] * b2) % 3, (k + k2) % 8)
G = list(product(range(7), range(3), range(3), range(3), range(8)))
n = len(G); idx = {g: g[0]*216 + g[1]*72 + g[2]*24 + g[3]*8 + g[4] for g in G}
e = (0, 0, 0, 0, 0)
S = [(0,0,0,0,0), (5,0,1,0,0), (2,0,0,2,2), (0,2,0,1,4), (0,1,2,1,4), (0,2,1,2,3), (0,1,0,1,7), (5,2,1,2,0), (3,1,1,1,0)]
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
    gens = {(1,0,0,0,0): (6,0,0,0,0), (0,1,0,0,0): (0,1,0,0,0), (0,0,1,0,0): (0,0,2,0,0), (0,0,0,1,0): (0,0,0,1,0), (0,0,0,0,1): (0,0,2,1,3)}
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
