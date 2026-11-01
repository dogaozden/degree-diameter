"""Lazebnik-Ustimenko graphs D(k,q) for k <= 4 over GF(2^e) or prime q, and quotients of D(4,q) by translations of the
last coordinate. Relations (points (p1,p11,p12,p21), lines [l1,l11,l12,l21]):
  l11 - p11 = l1 p1,  l12 - p12 = l11 p1,  l21 - p21 = l1 p11.
D(k,q) keeps the first k coordinates.  BFS eccentricity from one point and one line (the graphs are edge-transitive
on darts? not assumed: we report both and the max over a few random sources).
usage: python3 lu_graphs.py k q [C]   (C: for k = 4 and q = 2^e, quotient p21 mod an additive subgroup of order C)"""
import sys, random
import numpy as np
from collections import deque

def field(q):
    # returns add, mul tables for GF(q), q prime or 2^e (e <= 4)
    polys = {4: 0b10011 >> 0, 8: 0b1011, 16: 0b10011, 2: 0b11}
    if q in (2, 4, 8, 16):
        e = q.bit_length() - 1
        mod = {2: 0b11, 4: 0b111, 8: 0b1011, 16: 0b10011}[q]
        def gmul(a, b):
            r = 0
            while b:
                if b & 1: r ^= a
                b >>= 1; a <<= 1
                if a & q: a ^= mod
            return r
        add = np.array([[a ^ b for b in range(q)] for a in range(q)], dtype=np.int32)
        sub = add
        mul = np.array([[gmul(a, b) for b in range(q)] for a in range(q)], dtype=np.int32)
    else:
        add = np.array([[(a + b) % q for b in range(q)] for a in range(q)], dtype=np.int32)
        sub = np.array([[(a - b) % q for b in range(q)] for a in range(q)], dtype=np.int32)
        mul = np.array([[(a * b) % q for b in range(q)] for a in range(q)], dtype=np.int32)
    return add, sub, mul

def build(k, q, C=None):
    add, sub, mul = field(q)
    # coordinate ranges
    rng = [q] * k
    if C is not None:
        rng[3] = q // C          # p21 taken mod the subgroup {0..C-1} (low bits for q = 2^e): keep high bits
    def enc(v):
        x = 0
        for c, r in zip(v, rng):
            x = x * r + c
        return x
    n = int(np.prod(rng))
    adj = np.empty((2 * n, q), dtype=np.int64)
    import itertools
    for idx, p in enumerate(itertools.product(*[range(r) for r in rng])):
        p = list(p)
        for t, l1 in enumerate(range(q)):
            l = [l1]
            if k >= 2: l.append(add[p[1], mul[l1, p[0]]])            # l11 = p11 + l1 p1
            if k >= 3: l.append(add[p[2], mul[l[1], p[0]]])          # l12 = p12 + l11 p1
            if k >= 4:
                v = add[(p[3] * C) if C else p[3], mul[l1, p[1]]]     # l21 = p21 + l1 p11 (p21 lifted to a rep)
                l.append(v // C if C else v)
            u = enc(p); w = enc(l)
            adj[u, t] = n + w
    # line adjacency by inverting
    deg = np.zeros(2 * n, dtype=np.int64)
    for u in range(n):
        for t in range(q):
            w = adj[u, t]; adj[w, deg[w]] = u; deg[w] += 1
    assert (deg[n:] == q).all(), (deg[n:].min(), deg[n:].max())
    return n, adj

def ecc(adj, s):
    N = len(adj); d = np.full(N, -1, dtype=np.int64); d[s] = 0; dq = deque([s])
    while dq:
        u = dq.popleft()
        for w in adj[u]:
            if d[w] < 0: d[w] = d[u] + 1; dq.append(w)
    return int(d.max()), int((d < 0).sum())

if __name__ == '__main__':
    k, q = int(sys.argv[1]), int(sys.argv[2]); C = int(sys.argv[3]) if len(sys.argv) > 3 else None
    n, adj = build(k, q, C)
    srcs = [0, n] + [random.randrange(2 * n) for _ in range(4)]
    print(f'D({k},{q})' + (f'/C{C}' if C else ''), 'vertices', 2 * n, 'ecc (max dist, unreached):', [ecc(adj, s) for s in srcs])
