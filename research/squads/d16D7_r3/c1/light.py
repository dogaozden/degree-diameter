#!/usr/bin/env python3
"""light.py QUOT: light (weight 1/3) quotient vertices, their light-light adjacency and nine-neighbour counts."""
import sys
W = []; adj = []
with open(sys.argv[1]) as f:
    n = int(f.readline())
    for i in range(n):
        a = list(map(int, f.readline().split()))
        W.append(a[0]); adj.append(set(a[2:2 + a[1]]))
L = [v for v in range(n) if W[v] < 9]
print('n', n, 'light', len(L), 'light weight', sum(W[v] for v in L))
for v in L:
    nn = sum(1 for u in adj[v] if W[u] == 9)
    ll = sorted(u for u in adj[v] if W[u] < 9)
    print(v, 'w', W[v], 'nine-nbrs', nn, 'light-nbrs', ll)
nines = [v for v in range(n) if W[v] == 9]
ni = {v: i for i, v in enumerate(nines)}
print('nine subgraph vertices', len(nines), 'edges', sum(len(adj[v] & set(nines)) for v in nines) // 2)
