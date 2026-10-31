# list uncovered (source, base vertex, element) pairs of a vl solution (same semantics as tabu.c)
import sys
from collections import defaultdict
tok = open(sys.argv[2]).read().split(); m = int(tok[0])
mul = [[int(tok[1 + i * m + j]) for j in range(m)] for i in range(m)]
inv = [0] * m
for x in range(m):
    for y in range(m):
        if mul[x][y] == 0: inv[x] = y
lines = [l for l in open(sys.argv[1]) if l.strip() and not l.startswith('#')]
b, E = map(int, lines[0].split()[:2])
side = list(map(int, lines[1].split()))
edges = []
for l in lines[2:2 + E]:
    u, w, v = map(int, l.split()[:3])
    if side[u] == 1: u, w = w, u
    edges.append((u, w, v))
adj = defaultdict(list)
for e, (u, w, v) in enumerate(edges):
    adj[u].append((w, e, 0, v)); adj[w].append((u, e, 1, v))
# spanning tree (BFS from 0) as in tabu.c
seen = {0}; q = [0]; tree = set()
for x in q:
    for (y, e, d, v) in adj[x]:
        if y not in seen: seen.add(y); q.append(y); tree.add(e)
print("tree edges", sorted(tree), "free", [e for e in range(E) if e not in tree])
def cover(s):
    D = 5 if side[s] == 0 else 4
    C = set()
    stack = [(s, -1, 0, 0)]
    while stack:
        v, le, h, L = stack.pop()
        C.add((v, h))
        if L == D: continue
        for (w, e, d, val) in adj[v]:
            if e == le: continue
            g = inv[val] if d else val
            stack.append((w, e, mul[h][g], L + 1))
    return C
tot = 0
for s in range(b):
    C = cover(s)
    unc = [(v, h) for v in range(b) if not (side[s] == 1 and side[v] == 0) for h in range(m) if (v, h) not in C]
    tot += len(unc)
    print("source", s, "side", side[s], "uncovered", len(unc), unc[:12])
print("total uncovered", tot)
