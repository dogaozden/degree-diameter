#!/usr/bin/env python3
"""Independent check of glift: for every group in GROUPFILE and every base, enumerate ALL voltage assignments that are
the identity on a DFS spanning tree (no Aut reduction), build the lift (x, g) ~ (y, g*h), BFS diameter; collect nauty
canonical forms of the simple cubic lifts with diameter <= D. Compare with the canonical forms of glift's SOL lines.
Usage: crosscheck_g.py GROUPFILE BASES D GLIFT_OUT"""
import sys, itertools, subprocess, networkx as nx
from collections import deque
gfile, bases, D, gout = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
groups = {}; cur = None
toks = open(gfile).read().split(); i = 0
while i < len(toks):
    if toks[i] == 'G':
        N, gid = int(toks[i + 1]), int(toks[i + 2]); i += 4
        mul = [list(map(int, toks[i + r * N: i + (r + 1) * N])) for r in range(N)]; i += N * N
        groups[gid] = (N, mul)
    elif toks[i] == 'A':
        i += 2 + int(toks[i + 1])
    else: i += 1
blines = [l.split() for l in open(bases) if l.strip()]
def parse(b):
    nv, ns = int(b[0]), int(b[1]); E = []
    for j in range(ns):
        a, c, m = map(int, b[2 + 3 * j:5 + 3 * j]); E += [(a, c)] * m
    return nv, E
def lift(nv, E, volt, N, mul):
    G = nx.MultiGraph(); G.add_nodes_from(range(nv * N))
    for (a, b), h in zip(E, volt):
        for g in range(N): G.add_edge(a * N + g, b * N + mul[g][h])
    return G
def canon(gs):
    data = ''.join(nx.to_graph6_bytes(g, header=False).decode() for g in gs)
    return set(subprocess.run(['nauty-labelg', '-q'], input=data, capture_output=True, text=True).stdout.split())
def orient(nv, E, tree_kind):
    adj = {x: [] for x in range(nv)}
    for idx, (a, b) in enumerate(E): adj[a].append((b, idx)); adj[b].append((a, idx))
    side = {0: 0}; st = [0]; tree = set()
    while st:
        x = st.pop()
        for y, idx in adj[x]:
            if y not in side: side[y] = 1 - side[x]; tree.add(idx); st.append(y)
    return [(a, b) if side[a] == 0 else (b, a) for a, b in E], tree
mine = []
for b in blines:
    nv, E = parse(b); E, tree = orient(nv, E, 'dfs'); cot = [j for j in range(len(E)) if j not in tree]
    for gid, (N, mul) in groups.items():
        for vals in itertools.product(range(N), repeat=len(cot)):
            volt = [0] * len(E)
            for j, v in zip(cot, vals): volt[j] = v
            G = lift(nv, E, volt, N, mul)
            if any(d != 3 for _, d in nx.Graph(G).degree()): continue
            H = nx.Graph(G); ok = True
            for x in range(nv):
                dist = nx.single_source_shortest_path_length(H, x * N)
                if len(dist) < H.number_of_nodes() or max(dist.values()) > D: ok = False; break
            if ok: mine.append(H)
theirs = []
for l in open(gout):
    if not l.startswith('SOL'): continue
    f = l.split(); bid, gid = int(f[1]), int(f[2]); volt = list(map(int, f[4:]))
    nv, E = parse(blines[bid])
    adj = {x: [] for x in range(nv)}
    for a, c in E: adj[a].append(c); adj[c].append(a)
    side = {0: 0}; q = [0]
    for x in q:
        for y in adj[x]:
            if y not in side: side[y] = 1 - side[x]; q.append(y)
    E = [(a, c) if side[a] == 0 else (c, a) for a, c in E]
    N, mul = groups[gid]; G = nx.Graph(lift(nv, E, volt, N, mul))
    if all(d == 3 for _, d in G.degree()): theirs.append(G)
cm, ct = canon(mine), canon(theirs)
print(f"python: {len(mine)} lifts, {len(cm)} classes; glift: {len(theirs)} lifts, {len(ct)} classes; equal={cm == ct}")
