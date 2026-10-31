#!/usr/bin/env python3
"""The (9,5) graph on 3,000 vertices from its formula alone (no GAP): Haar graph H(G,S) of
G = (C5 x C5 x C5) : (C3 : C4) = SmallGroup(1500,113), elements (a,b,c,i,j) = v s^i u^j with v = (a,b,c) in F5^3,
s of order 3, u of order 4, u s u^-1 = s^-1, and s, u acting on F5^3 by the matrices (columns = images of the basis)
  Rs = [[1,0,0],[0,2,3],[0,1,2]],  Ru = [[3,0,0],[0,2,2],[0,1,3]]   (mod 5),
so the product is (v, i, j)(v', i', j') = (v + Rs^i Ru^j v', i + (-1)^j i', j + j').
S = {(0,0,0,0,0), (4,0,0,1,2), (0,2,3,1,2), (3,0,0,2,2), (2,0,1,2,2), (3,2,1,2,1), (4,3,1,1,3), (0,0,2,2,1),
(0,4,1,1,3)}; (g,A) ~ (s g, B).  Vertex numbers: g = (a,b,c,i,j) -> a*300 + b*60 + c*12 + i*4 + j on side A, plus 1500
on side B.
Self-dual: beta, the automorphism with (1,0,0,0,0) -> (1,0,0,0,0), (0,1,0,0,0) -> (0,2,1,0,0), (0,0,1,0,0) -> (0,2,3,0,0),
s -> s^2, u -> u, is an involution with beta(s)^-1 in S for s in S, so the graph is also the Cayley graph of G : <tau>
(tau g tau = beta(g)) with T = S tau; built here too.
usage: build_d9D5_n3000.py HAAR.edges [CAYLEY.edges]   (BFS from every vertex for the Haar graph)
"""
import sys
from collections import deque
from itertools import product
Rs = [[1,0,0],[0,2,3],[0,1,2]]; Ru = [[3,0,0],[0,2,2],[0,1,3]]
def mm(A, B): return [[sum(A[r][t] * B[t][c] for t in range(3)) % 5 for c in range(3)] for r in range(3)]
I3 = [[1,0,0],[0,1,0],[0,0,1]]
def mpow(A, k):
    R = I3
    for _ in range(k): R = mm(R, A)
    return R
RM = {(i, j): mm(mpow(Rs, i), mpow(Ru, j)) for i in range(3) for j in range(4)}
def mul(x, y):
    M = RM[(x[3], x[4])]
    v = [(x[r] + sum(M[r][t] * y[t] for t in range(3))) % 5 for r in range(3)]
    return (v[0], v[1], v[2], (x[3] + (-1) ** x[4] * y[3]) % 3, (x[4] + y[4]) % 4)
G = list(product(range(5), range(5), range(5), range(3), range(4)))
n = len(G); idx = {g: g[0]*300 + g[1]*60 + g[2]*12 + g[3]*4 + g[4] for g in G}
e = (0, 0, 0, 0, 0)
S = [(0,0,0,0,0), (4,0,0,1,2), (0,2,3,1,2), (3,0,0,2,2), (2,0,1,2,2), (3,2,1,2,1), (4,3,1,1,3), (0,0,2,2,1), (0,4,1,1,3)]
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
    gens = {(1,0,0,0,0): (1,0,0,0,0), (0,1,0,0,0): (0,2,1,0,0), (0,0,1,0,0): (0,2,3,0,0), (0,0,0,1,0): (0,0,0,2,0), (0,0,0,0,1): (0,0,0,0,1)}
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
