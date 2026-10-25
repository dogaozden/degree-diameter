#!/usr/bin/env python3
"""swap12.py OG SOL: (1,2)-swaps of an orbit-graph independent set: remove u in S, insert two non-adjacent outside
vertices whose only neighbour in S is u. Prints the number of such swap opportunities."""
import sys
g, s = sys.argv[1], sys.argv[2]
with open(g) as f:
    M, E = map(int, f.readline().split())
    nb = [None] * M
    for line in f:
        a = list(map(int, line.split()))
        nb[a[0]] = a[3:3 + a[2]]
S = set(int(l) for l in open(s) if l.strip())
cnt = [0] * M; who = [-1] * M
for v in S:
    for u in nb[v]:
        cnt[u] += 1; who[u] = v
L = {}
for x in range(M):
    if x not in S and cnt[x] == 1:
        L.setdefault(who[x], []).append(x)
found = 0
nbs = {x: set(nb[x]) for x in range(M)}
for u, lst in L.items():
    for i in range(len(lst)):
        for j in range(i + 1, len(lst)):
            if lst[j] not in nbs[lst[i]]:
                found += 1
                if found <= 3: print('swap: remove', u, 'insert', lst[i], lst[j])
print(s, 'size', len(S), 'one-conflict vertices', sum(len(v) for v in L.values()), 'removable with (1,2)-swap', len(L), 'swap pairs', found)
