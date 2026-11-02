#!/usr/bin/env python3
"""autos.py BASE.txt: enumerate all automorphisms of a small graph (lift format), side-preserving, find order-3 ones; write BASE3.perm."""
import sys
path = sys.argv[1]
L = open(path).read().split()
N = int(L[0]); E = set()
for i in range(1, len(L), 2):
    u, v = int(L[i]), int(L[i+1]); E.add((min(u, v), max(u, v)))
adj = [set() for _ in range(N)]
for u, v in E: adj[u].add(v); adj[v].add(u)
h = N // 2
# BFS order from vertex 0
order = [0]; seen = {0}
for x in order:
    for y in sorted(adj[x]):
        if y not in seen: seen.add(y); order.append(y)
autos = []
img = [-1] * N; used = [False] * N
def bt(i):
    if i == N:
        autos.append(img[:]); return
    v = order[i]
    # candidates: must be adjacent to image of an already-mapped neighbour
    cands = range(N)
    prev = [u for u in adj[v] if img[u] >= 0]
    if prev:
        cands = adj[img[prev[0]]]
    for c in cands:
        if used[c]: continue
        ok = True
        for u in range(N):
            if img[u] >= 0 and ((u in adj[v]) != (img[u] in adj[c])):
                ok = False; break
        if not ok: continue
        if (v < h) != (c < h): continue
        img[v] = c; used[c] = True
        bt(i + 1)
        img[v] = -1; used[c] = False
bt(0)
print('automorphisms (side preserving):', len(autos))
def order_of(p):
    q = list(range(N)); k = 0
    while True:
        q = [p[x] for x in q]; k += 1
        if q == list(range(N)): return k
from collections import Counter
print('orders:', Counter(order_of(p) for p in autos))
o3 = [p for p in autos if order_of(p) == 3]
if o3:
    out = path.rsplit('.', 1)[0] + '3.perm'
    open(out, 'w').write(' '.join(map(str, o3[0])) + '\n')
    print('wrote', out, 'example', o3[0])
