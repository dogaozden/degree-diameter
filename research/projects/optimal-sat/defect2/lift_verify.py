#!/usr/bin/env python3
"""Theorem Q converse, checked by computer: from an A (npy) with a GF(2) signing, build the bipartite incidence graph
(quad c: points 2c,2c+1, lines 2c,2c+1; arc c->d with sign +: point 2c on line 2d, point 2c+1 on line 2d+1; sign -:
crossed) and check max degree k, order 2k(k-1) and diameter 3 by BFS from every vertex."""
import sys, itertools
import numpy as np
from signs_gf2 import squares

def signing(A):
    sq = squares(A)
    arcs = sorted({a for s in sq for a in s}); idx = {a: i for i, a in enumerate(arcs)}; n = len(arcs)
    piv = {}
    for s in sq:
        v = 1 << n
        for a in s: v ^= 1 << idx[a]
        while v & ((1 << n) - 1):
            col = (v & ((1 << n) - 1)).bit_length() - 1
            if col in piv: v ^= piv[col]
            else: piv[col] = v; break
        else:
            if v >> n & 1: return None
    sol = {}
    for col in sorted(piv):
        v = piv[col]; val = v >> n & 1
        for c2 in range(col):
            if v >> c2 & 1: val ^= sol.get(c2, 0)
        sol[col] = val
    return {a: sol.get(idx[a], 0) for a in arcs} | {}

def lift(A, sg):
    m = len(A); n = 2 * m
    adj = [set() for _ in range(2 * n)]  # points 0..n-1, lines n..2n-1
    def e(p, l): adj[p].add(n + l); adj[n + l].add(p)
    for c in range(m):
        for a_ in (0, 1):
            for b in (0, 1): e(2 * c + a_, 2 * c + b)
    for c in range(m):
        for d in range(m):
            if A[c, d]:
                s = sg.get((c, d), 0)
                e(2 * c, 2 * d + s); e(2 * c + 1, 2 * d + 1 - s)
    return adj

def diameter(adj):
    N = len(adj); D = 0
    for s in range(N):
        dist = [-1] * N; dist[s] = 0; q = [s]
        for u in q:
            for v in adj[u]:
                if dist[v] < 0: dist[v] = dist[u] + 1; q.append(v)
        if min(dist) < 0: return None
        D = max(D, max(dist))
    return D

if __name__ == '__main__':
    A = np.load(sys.argv[1]); k = int(A.sum(1)[0]) + 2
    sg = signing(A)
    if sg is None: print('no signing'); sys.exit(1)
    adj = lift(A, sg)
    degs = {len(x) for x in adj}
    print(f'k={k}: vertices {len(adj)} (expected {2 * k * (k - 1)}), degrees {degs}, diameter {diameter(adj)}')
