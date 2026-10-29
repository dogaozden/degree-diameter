#!/usr/bin/env python3
"""For a base multigraph (vl base file), count distinct coefficient vectors (abelian voltage sums) of non-backtracking
walks of length <= D (right parity) from each source to each target. In an abelian lift the number of sheets of a
target that a source can reach is at most this count. usage: walkvec.py BASE [D]"""
import sys
from collections import defaultdict
lines = [l for l in open(sys.argv[1]) if l.strip() and not l.startswith('#')]
D = int(sys.argv[2]) if len(sys.argv) > 2 else 5
b, E = map(int, lines[0].split()); side = list(map(int, lines[1].split()))
edges = [tuple(map(int, l.split()[:2])) for l in lines[2:2 + E]]
adj = defaultdict(list)
for e, (u, w) in enumerate(edges):
    if side[u] == 1: u, w = w, u
    adj[u].append((w, e, 1)); adj[w].append((u, e, -1))
res = {}
for s in range(b):
    L = D if side[s] == 0 else D - 1
    vecs = defaultdict(set)
    def dfs(v, laste, vec, k):
        if side[s] == 0 or side[v] == 1: vecs[v].add(tuple(vec))
        if k == L: return
        for (w, e, sg) in adj[v]:
            if e == laste: continue
            vec[e] += sg; dfs(w, e, vec, k + 1); vec[e] -= sg
    dfs(s, -1, [0] * E, 0)
    res[s] = {v: len(x) for v, x in vecs.items()}
    print(s, 'side', side[s], {v: len(x) for v, x in sorted(vecs.items())})
