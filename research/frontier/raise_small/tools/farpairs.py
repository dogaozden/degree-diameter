#!/usr/bin/env python3
"""farpairs.py SOL m k r D: list the far (root, vertex) pairs of a salift_s state over Z_m x|_r Z_k.
Root (u, e) for each base vertex u; a vertex (w, g) is far if its distance from (u, e) exceeds D. Prints each far pair
as root u -> (w, (a, j)), with the element order, whether it is central, and g relative to the voltages."""
import sys
from collections import deque
from math import gcd

sol, m, k, r, D = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
L = [l.split() for l in open(sol) if l.strip() and not l.startswith('#')]
N = int(L[0][0]); base = [tuple(map(int, t[:3])) for t in L[1:]]
dec = lambda x: (x // k, x % k); enc = lambda a, j: a * k + j
rp = [pow(r, j, m) for j in range(k)]
def mul(g, h):
    (a, j), (b, l) = dec(g), dec(h); return enc((a + rp[j] * b) % m, (j + l) % k)
def inv(g):
    a, j = dec(g); jj = (-j) % k; return enc((-rp[jj] * a) % m, jj)
def order(g):
    x, o = g, 1
    while x != 0: x = mul(x, g); o += 1
    return o
nb = 1 + max(max(u, v) for u, v, _ in base)
adj = [[] for _ in range(nb)]
for u, v, x in base:
    adj[u].append((v, x)); adj[v].append((u, inv(x)))
print("voltages:", [(u, v, dec(x)) for u, v, x in base])
total = 0
for u in range(nb):
    dist = {(u, 0): 0}; q = deque([(u, 0)])
    while q:
        w, g = q.popleft(); d = dist[(w, g)]
        if d == D: continue
        for (w2, x) in adj[w]:
            y = (w2, mul(g, x))
            if y not in dist: dist[y] = d + 1; q.append(y)
    for w in range(nb):
        for g in range(N):
            if (w, g) not in dist:
                total += 1
                cen = all(mul(g, h) == mul(h, g) for h in range(0, N, max(1, N // 50)))
                print(f"root {u} -> ({w}, {dec(g)}) order {order(g)} central~{cen}")
print("far pairs:", total)
