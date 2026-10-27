#!/usr/bin/env python3
"""Compare zplift and jsearch solution sets up to isomorphism of the lifted graphs (nauty labelg canonical forms).
Usage: compare_iso.py P ZPLIFT_OUT BASES JSEARCH_OUT"""
import sys, subprocess, networkx as nx
P, zout, bases, jout = int(sys.argv[1]), sys.argv[2], sys.argv[3], sys.argv[4]
blines = [l for l in open(bases) if l.strip()]
def lift(edges, p):  # edges: list of (a, b, t), a on side 0
    G = nx.Graph()
    for a, b, t in edges:
        for g in range(p):
            G.add_edge(a * p + g, b * p + (g + t) % p)
    return G
def canon(graphs):
    data = ''.join(nx.to_graph6_bytes(G, header=False).decode() for G in graphs)
    out = subprocess.run(['nauty-labelg', '-q'], input=data, capture_output=True, text=True).stdout.split()
    return set(out)
Z = []
for l in open(zout):
    if not l.startswith('SOL'): continue
    f = l.split(); bid = int(f[1]); volt = list(map(int, f[4:]))
    b = blines[bid].split(); nv, ns = int(b[0]), int(b[1]); E = []
    for i in range(ns):
        a, c, m = map(int, b[2 + 3 * i:5 + 3 * i]); E += [(a, c)] * m
    adj = {i: [] for i in range(nv)}
    for a, c in E: adj[a].append(c); adj[c].append(a)
    side = {0: 0}; q = [0]
    for x in q:
        for y in adj[x]:
            if y not in side: side[y] = 1 - side[x]; q.append(y)
    Z.append(lift([(a, c, t) if side[a] == 0 else (c, a, t) for (a, c), t in zip(E, volt)], P))
J = []
for l in open(jout):
    if not l.startswith('SOL'): continue
    J.append(lift([tuple(map(int, s.replace('-', ':').split(':'))) for s in l.split()[2:]], P))
Z = [G for G in Z if all(d == 3 for _, d in G.degree())]  # simple cubic lifts only (no double edges)
cz, cj = canon(Z), canon(J)
print(f"zplift: {len(Z)} solutions, {len(cz)} iso classes; jsearch: {len(J)} solutions, {len(cj)} iso classes; "
      f"equal={cz == cj} only_z={len(cz - cj)} only_j={len(cj - cz)}")
