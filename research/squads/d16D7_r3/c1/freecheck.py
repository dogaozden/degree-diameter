#!/usr/bin/env python3
"""freecheck.py OG SOL...: for each orbit-graph solution, count outside vertices with no neighbour in the solution (free),
then greedily add free vertices (min-degree first) and report the size of the maximal extension."""
import sys
g = sys.argv[1]
with open(g) as f:
    M, E = map(int, f.readline().split())
    nb = [None] * M
    for line in f:
        a = list(map(int, line.split()))
        nb[a[0]] = a[3:3 + a[2]]
for s in sys.argv[2:]:
    S = set(int(l) for l in open(s) if l.strip())
    cnt = [0] * M   # number of neighbours in S
    for v in S:
        for u in nb[v]:
            cnt[u] += 1
    free = [v for v in range(M) if v not in S and cnt[v] == 0]
    ones = [v for v in range(M) if v not in S and cnt[v] == 1]
    # greedy maximal extension
    T = set(S); c2 = list(cnt)
    added = 0
    for v in free:
        if c2[v] == 0 and v not in T:
            T.add(v); added += 1
            for u in nb[v]: c2[u] += 1
    print(s, 'size', len(S), 'free', len(free), 'one-conflict', len(ones), 'greedy_extension_adds', added, 'size_after', len(T))
