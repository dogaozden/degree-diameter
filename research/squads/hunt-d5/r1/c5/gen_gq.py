#!/usr/bin/env python3
"""Base multigraph for Z_9 lifts: incidence graph of GQ W(5) (156 points, 156 lines, 6-regular)
plus 3 extra perfect matchings points-lines disjoint from the incidence and from each other.
Usage: gen_gq.py OUT.base SEED"""
import sys, random
q = 5
out, seed = sys.argv[1], int(sys.argv[2])
rng = random.Random(seed)
def normalize(v):
    for x in v:
        if x % q:
            inv = pow(x, q - 2, q)
            return tuple((y * inv) % q for y in v)
    return None
pts = sorted({normalize(v) for v in __import__('itertools').product(range(q), repeat=4) if any(v)})
assert len(pts) == (q**4 - 1) // (q - 1)
idx = {p: i for i, p in enumerate(pts)}
def B(x, y):  # symplectic form
    return (x[0]*y[1] - x[1]*y[0] + x[2]*y[3] - x[3]*y[2]) % q
lines = set()
n = len(pts)
for i in range(n):
    for j in range(i + 1, n):
        p, r = pts[i], pts[j]
        if B(p, r) == 0:
            span = set()
            for a in range(q):
                for b in range(q):
                    if a or b:
                        v = tuple((a*p[k] + b*r[k]) % q for k in range(4))
                        span.add(idx[normalize(v)])
            lines.add(frozenset(span))
lines = sorted(lines, key=lambda s: sorted(s))
assert len(lines) == n and all(len(L) == q + 1 for L in lines), (len(lines))
inc = [[False]*n for _ in range(n)]   # inc[p][l]
for l, L in enumerate(lines):
    for p in L: inc[p][l] = True
deg = [sum(inc[p]) for p in range(n)]
assert all(d == q + 1 for d in deg)
used = [set() for _ in range(n)]   # used[p]: lines already joined to p
for p in range(n):
    for l in range(n):
        if inc[p][l]: used[p].add(l)
matchings = []
def kuhn(order_l, adj):
    match_l = [-1]*n; match_p = [-1]*n
    def try_(p, seen):
        for l in adj[p]:
            if l in seen: continue
            seen.add(l)
            if match_l[l] < 0 or try_(match_l[l], seen):
                match_l[l] = p; match_p[p] = l; return True
        return False
    import sys as _s; _s.setrecursionlimit(10000)
    for p in range(n):
        if not try_(p, set()): return None
    return [(p, match_p[p]) for p in range(n)]
for _ in range(3):
    adj = []
    for p in range(n):
        a = [l for l in range(n) if l not in used[p]]
        rng.shuffle(a); adj.append(a)
    M = kuhn(None, adj)
    assert M is not None
    for p, l in M:
        used[p].add(l); matchings.append((p, l))
edges = []
for p in range(n):
    for l in range(n):
        if inc[p][l]: edges.append((p, n + l))
edges += [(p, n + l) for p, l in matchings]
with open(out, 'w') as f:
    f.write(f"{2*n} {len(edges)}\n")
    for u, v in edges: f.write(f"{u} {v}\n")
print("base", 2*n, "vertices", len(edges), "edges; degree 9 check:",
      all(sum(1 for e in edges if e[0] == p) == 9 for p in range(n)))
