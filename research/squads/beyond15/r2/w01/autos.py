#!/usr/bin/env python3
# autos.py BASE [maxfound]: side-preserving automorphisms of a bipartite cubic base (lift format), via backtracking
# with BFS-consistency. Prints the involutions (as perm lines) found, one per line, for use as liftsym PERM files.
import sys
L = open(sys.argv[1]).read().split()
b = int(L[0]); E = [(int(L[i]), int(L[i+1])) for i in range(1, len(L), 2)]
adj = [set() for _ in range(b)]
for u, v in E: adj[u].add(v); adj[v].add(u)
maxf = int(sys.argv[2]) if len(sys.argv) > 2 else 10**9
side = [0 if v < b // 2 else 1 for v in range(b)]
order = []  # BFS order from 0
seen = {0}; q = [0]
for x in q:
    for y in sorted(adj[x]):
        if y not in seen: seen.add(y); q.append(y)
order = q
found = []
def rec(img, i):
    if len(found) >= maxf: return
    if i == b:
        found.append(img[:]); return
    v = order[i]
    if img[v] >= 0:
        rec(img, i + 1); return
    # candidate images: must be adjacent to images of already-mapped neighbours
    mapped_nb = [w for w in adj[v] if img[w] >= 0]
    used = set(x for x in img if x >= 0)
    if mapped_nb:
        cands = set(adj[img[mapped_nb[0]]])
    else:
        cands = set(range(b))
    for c in cands:
        if c in used or side[c] != side[v] or len(adj[c]) != len(adj[v]): continue
        ok = True
        for w in mapped_nb:
            if img[w] not in adj[c]: ok = False; break
        if not ok: continue
        # neighbourhood check on mapped vertices
        img[v] = c
        good = True
        for w in adj[v]:
            if img[w] >= 0 and img[w] not in adj[c]: good = False; break
        if good:
            rec(img, i + 1)
        img[v] = -1
        if len(found) >= maxf: return
# fix image of vertex 0 to several choices to bound search
img = [-1] * b
cnt = 0
import itertools
def search_all():
    global found
    rec(img, 0)
search_all()
def is_aut(p):
    s = set(frozenset((p[u], p[v])) for u, v in E)
    return s == set(frozenset(e) for e in E)
res = [p for p in found if is_aut(p) and all(p[x] != x for x in range(0))]
inv = [p for p in res if all(p[p[x]] == x for x in range(b))]
print('automorphisms (side-preserving) found:', len(res), 'involutions:', len(inv), file=sys.stderr)
for p in inv:
    fixed = sum(1 for x in range(b) if p[x] == x)
    print(fixed, ' '.join(map(str, p)))
