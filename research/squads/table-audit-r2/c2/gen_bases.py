#!/usr/bin/env python3
# Writes cubic bipartite base multigraphs for card c2: "b E" then E lines "u w".
import os
from collections import deque
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bases")
os.makedirs(OUT, exist_ok=True)

def bipartite(b, edges):
    adj = [[] for _ in range(b)]
    for u, w in edges:
        adj[u].append(w); adj[w].append(u)
    col = [-1] * b; col[0] = 0; q = deque([0]); ok = True
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

def gp(n, k):
    e = []
    for i in range(n):
        e.append((i, (i + 1) % n))
        e.append((n + i, n + (i + k) % n))
        e.append((i, n + i))
    return (2 * n, sorted(set(tuple(sorted(x)) for x in e)))

def lcf(n, pattern, reps):
    L = pattern * reps
    e = set()
    for i in range(n):
        e.add(tuple(sorted((i, (i + 1) % n))))
        e.add(tuple(sorted((i, (i + L[i % len(L)]) % n))))
    return (n, sorted(e))

bases = {}
bases["desargues"] = gp(10, 3)                 # GP(10,3), 20 vertices
bases["dyck"] = lcf(32, [5, -9, 7, -7, 9, -5], 4 if False else 1) if False else None
# Dyck graph: LCF [5,-9,7,-7,9,-5]^4 on a 32-cycle
bases["dyck"] = lcf(32, [5, -9, 7, -7, 9, -5], 0) if False else (32, sorted(set(
    tuple(sorted(x)) for x in
    [(i, (i + 1) % 32) for i in range(32)] +
    [(i, (i + [5, -9, 7, -7, 9, -5][i % 6]) % 32) for i in range(32)])))
for name, (b, edges) in bases.items():
    assert len(edges) == 3 * b // 2, (name, len(edges))
    assert cubic(b, edges), name
    assert bipartite(b, edges), name
    with open(os.path.join(OUT, name + ".txt"), "w") as f:
        f.write(f"{b} {len(edges)}\n")
        for u, w in edges:
            f.write(f"{u} {w}\n")
    print(name, "b=", b, "E=", len(edges), "cubic+bipartite ok")
