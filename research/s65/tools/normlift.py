#!/usr/bin/env python3
"""Re-normalise a vl lift so that the BFS spanning tree from base vertex 0 (in edge order, as kdesc/tabu/kopt pick it)
has identity voltages: new voltage of edge a -> b is q_a^-1 g q_b (same lift up to isomorphism).
usage: normlift.py SOL GROUP OUT"""
import sys
sol, grp, out = sys.argv[1:4]
L = [l for l in open(sol).read().split('\n') if l.strip() and not l.startswith('#')]
if L[0].startswith('SOL'): L[0] = L[0][3:]
b, E = map(int, L[0].split()); side = list(map(int, L[1].split()))
ed = [list(map(int, x.split())) for x in L[2:2 + E]]
tok = open(grp).read().split(); m = int(tok[0]); mul = [list(map(int, tok[1 + i * m:1 + (i + 1) * m])) for i in range(m)]
inv = [r.index(0) for r in mul]
for e in ed:
    if side[e[0]] == 1: e[0], e[1] = e[1], e[0]
adj = [[] for _ in range(b)]
for k, (u, w, g) in enumerate(ed): adj[u].append((w, k)); adj[w].append((u, k))
q = [None] * b; q[0] = 0; queue = [0]
while queue:
    x = queue.pop(0)
    for y, k in adj[x]:
        if q[y] is None:
            u, w, g = ed[k]
            if x == u: q[y] = mul[inv[g]][q[x]]      # q_w = g^-1 q_u
            else: q[y] = mul[g][q[x]]               # q_u = g q_w
            queue.append(y)
with open(out, 'w') as f:
    f.write(f"{b} {E}\n" + " ".join(map(str, side)) + "\n")
    for u, w, g in ed: f.write(f"{u} {w} {mul[mul[inv[q[u]]][g]][q[w]]}\n")
