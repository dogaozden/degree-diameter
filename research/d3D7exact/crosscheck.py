#!/usr/bin/env python3
"""Independent check of zplift counts: enumerate every voltage assignment that is 0 on a DFS spanning tree (a different
tree from zplift's BFS tree), build the Z_p lift, compute its diameter by BFS, count lifts that are bipartite-diameter
<= D. zplift counts one assignment per Z_p^* scaling class, so expect count = zplift_count * (p - 1).
Usage: crosscheck.py BASES p D"""
import sys, itertools
from collections import deque
bases, p, D = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
tot = 0
for line in open(bases):
    f = line.split()
    if not f: continue
    nv, ns = int(f[0]), int(f[1]); E = []
    for i in range(ns):
        a, b, m = map(int, f[2 + 3 * i:5 + 3 * i]); E += [(a, b)] * m
    adj = {i: [] for i in range(nv)}
    for i, (a, b) in enumerate(E):
        adj[a].append((b, i)); adj[b].append((a, i))
    side = {0: 0}; st = [0]; tree = set()
    while st:  # DFS tree
        x = st.pop()
        for y, i in adj[x]:
            if y not in side:
                side[y] = 1 - side[x]; tree.add(i); st.append(y)
    E = [(a, b) if side[a] == 0 else (b, a) for a, b in E]
    cot = [i for i in range(len(E)) if i not in tree]
    n = nv * p; cnt = 0
    for vals in itertools.product(range(p), repeat=len(cot)):
        volt = [0] * len(E)
        for i, v in zip(cot, vals): volt[i] = v
        A = [[] for _ in range(n)]
        for (a, b), t in zip(E, volt):
            for g in range(p):
                A[a * p + g].append(b * p + (g + t) % p); A[b * p + (g + t) % p].append(a * p + g)
        ok = True
        for x in range(nv):  # by symmetry, BFS from (x, 0) suffices
            s = x * p; dist = [-1] * n; dist[s] = 0; dq = deque([s])
            while dq:
                y = dq.popleft()
                for z in A[y]:
                    if dist[z] < 0: dist[z] = dist[y] + 1; dq.append(z)
            if min(dist) < 0 or max(dist) > D: ok = False; break
        cnt += ok
    tot += cnt
print(tot)
