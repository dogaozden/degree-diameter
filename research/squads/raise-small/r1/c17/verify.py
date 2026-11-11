#!/usr/bin/env python3
"""verify.py GROUPTAB BASE BEST: recount the cost of a .best state independently (plain BFS from (u,e) for every base
root u, count lift vertices at distance > D). Usage: verify.py GROUPTAB BASE BEST D"""
import sys
from collections import deque
tab, base, best, D = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
toks = open(tab).read().split()
N = int(toks[1]); M = list(map(int, toks[4:4 + N * N]))
mul = lambda g, h: M[g * N + h]
inv = [next(h for h in range(N) if M[g * N + h] == 0) for g in range(N)]
bt = open(base).read().split()
NB, NE = int(bt[0]), int(bt[1])
E = [(int(bt[2 + 2 * i]), int(bt[3 + 2 * i])) for i in range(NE)]
bl = open(best).read().split()
assert int(bl[0]) == N
vol = list(map(int, bl[2:2 + NE]))
nbr = [[] for _ in range(NB)]
for (p, l), x in zip(E, vol):
    nbr[p].append((l, x)); nbr[l].append((p, inv[x]))
n = NB * N
cost = 0
for u in range(NB):
    dist = [-1] * n; s = u * N; dist[s] = 0; dq = deque([s])
    while dq:
        y = dq.popleft(); d = dist[y]
        if d == D: continue
        b, g = divmod(y, N)
        for (v, x) in nbr[b]:
            z = v * N + mul(g, x)
            if dist[z] < 0:
                dist[z] = d + 1; dq.append(z)
    cost += sum(1 for z in range(n) if dist[z] < 0)
print("recounted cost", cost, "recorded", bl[1])
