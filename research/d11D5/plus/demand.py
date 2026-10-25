"""Demand graphs of a DM base: same-side pairs at pure distance >= 6, or at distance 4 with one geodesic.
σ must map demanded point pairs to concurrent lines and demanded line pairs to collinear points.
usage: python3 demand.py base.in"""
import sys
from collections import Counter
f = open(sys.argv[1]); n, dg = map(int, f.readline().split())
L = [list(map(int, f.readline().split())) for _ in range(n)]
sig = [int(f.readline()) for _ in range(n)]
P = [[] for _ in range(n)]
for l in range(n):
    for p in L[l]: P[p].append(l)
def side_counts(adj1, adj2):
    # for each vertex x of side 1: counts of walks of length 2 and 4 to side-1 vertices (non-backtracking), distance
    dem = []; dist4one = 0; far = 0; hist = Counter()
    for x in range(n):
        c2 = Counter()
        for a in adj1[x]:
            for y in adj2[a]:
                if y != x: c2[y] += 1
        c4 = Counter()
        for a in adj1[x]:
            for y in adj2[a]:
                if y == x: continue
                for b in adj1[y]:
                    if b == a: continue
                    for z in adj2[b]:
                        if z != y: c4[z] += 1
        for z in range(n):
            if z <= x: continue
            if c2[z]: continue
            g = c4[z]
            hist[min(g, 10)] += 1
            if g == 0: far += 1; dem.append((x, z))
            elif g == 1: dist4one += 1; dem.append((x, z))
    return dem, far, dist4one, hist
dP, farP, oneP, hP = side_counts(P, L)
dL, farL, oneL, hL = side_counts(L, P)
print("points: far pairs", farP, "single-geodesic pairs", oneP, "hist", sorted(hP.items()))
print("lines : far pairs", farL, "single-geodesic pairs", oneL, "hist", sorted(hL.items()))
Lset = [set(s) for s in L]
inv = [0] * n
for p in range(n): inv[sig[p]] = p
bad = 0
for x, z in dP:
    if not (Lset[sig[x]] & Lset[sig[z]]): bad += 1
colp = [set() for _ in range(n)]
for s in L:
    for a in s: colp[a].update(s)
for x, z in dL:
    if inv[z] not in colp[inv[x]]: bad += 1
print("unsatisfied demands under current sigma:", bad)
from collections import defaultdict
for name, dem in (("points", dP), ("lines", dL)):
    g = defaultdict(set)
    for a, b in dem: g[a].add(b); g[b].add(a)
    degs = sorted(((len(v), k) for k, v in g.items()), reverse=True)
    print(name, "demand graph: vertices", len(g), "edges", len(dem), "top degrees", degs[:8])
    # triangles
    tri = sum(1 for a in g for b in g[a] for c in g[b] if a < b < c and c in g[a])
    print("  triangles", tri)
