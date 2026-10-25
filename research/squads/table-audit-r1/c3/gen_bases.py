#!/usr/bin/env python3
# Writes cubic bipartite base multigraphs as edge lists: first line "b E", then E lines "u w".
import os, sys
from collections import deque

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bases")
os.makedirs(OUT, exist_ok=True)

def bipartite(b, edges):
    adj = [[] for _ in range(b)]
    for u, w in edges:
        adj[u].append(w); adj[w].append(u)
    col = [-1] * b
    col[0] = 0
    q = deque([0])
    ok = True
    while q:
        x = q.popleft()
        for y in adj[x]:
            if col[y] < 0:
                col[y] = 1 - col[x]; q.append(y)
            elif col[y] == col[x]:
                ok = False
    return ok and all(c >= 0 for c in col)

def cubic(b, edges):
    deg = [0] * b
    for u, w in edges:
        deg[u] += 1; deg[w] += 1
    return all(d == 3 for d in deg)

bases = {}
bases["theta"] = (2, [(0, 1), (0, 1), (0, 1)])
bases["k33"] = (6, [(a, b) for a in range(3) for b in range(3, 6)])
bases["q3"] = (8, [(v, v ^ (1 << i)) for v in range(8) for i in range(3) if v < (v ^ (1 << i))])
# Heawood = incidence graph of the Fano plane: points 0..6, lines 7..13 = {j, j+1, j+3} mod 7
bases["heawood"] = (14, [(p, 7 + j) for j in range(7) for p in (j, (j + 1) % 7, (j + 3) % 7)])
# Moebius-Kantor GP(8,3): outer u_i = i, inner v_i = 8 + i
mk = []
for i in range(8):
    mk.append((i, (i + 1) % 8)); mk.append((8 + i, 8 + (i + 3) % 8)); mk.append((i, 8 + i))
bases["mobius_kantor"] = (16, mk)
# Pappus = LCF [5,7,-7,7,-7,-5]^3 on an 18-cycle
L = [5, 7, -7, 7, -7, -5] * 3
pap = set()
for i in range(18):
    pap.add(tuple(sorted((i, (i + 1) % 18))))
    pap.add(tuple(sorted((i, (i + L[i]) % 18))))
bases["pappus"] = (18, sorted(pap))
# 4-vertex cubic bipartite multigraph (parts {0,1}, {2,3}, doubled edges 0-2 and 1-3)
bases["k4multi"] = (4, [(0, 2), (0, 2), (0, 3), (1, 2), (1, 3), (1, 3)])

for name, (b, edges) in bases.items():
    assert cubic(b, edges), name
    assert bipartite(b, edges), name
    with open(os.path.join(OUT, name + ".txt"), "w") as f:
        f.write(f"{b} {len(edges)}\n")
        for u, w in edges:
            f.write(f"{u} {w}\n")
    print(name, "b=", b, "E=", len(edges), "ok")
