#!/usr/bin/env python3
"""GQ W(q) incidence base + k extra random perfect matchings (points-lines), for q in {4,5}.
Usage: gen_gq2.py q extra_matchings SEED OUT.base"""
import sys, random, itertools
q, extra, seed, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
rng = random.Random(seed)
if q == 5:
    add = lambda a, b: (a + b) % 5
    mul = lambda a, b: (a * b) % 5
    neg = lambda a: (-a) % 5
    inv = lambda a: pow(a, 3, 5)
    ZERO, ONE = 0, 1
else:  # GF(4): 0,1,2=w,3=w^2=w+1 ; addition = XOR
    MT = [[0,0,0,0],[0,1,2,3],[0,2,3,1],[0,3,1,2]]
    add = lambda a, b: a ^ b
    mul = lambda a, b: MT[a][b]
    neg = lambda a: a
    inv = lambda a: [None,1,3,2][a]
    ZERO, ONE = 0, 1
def normalize(v):
    for x in v:
        if x != ZERO:
            c = inv(x)
            return tuple(mul(c, y) for y in v)
    return None
pts = sorted({normalize(v) for v in itertools.product(range(q), repeat=4) if any(v)})
n = len(pts); assert n == (q**4 - 1) // (q - 1)
idx = {p: i for i, p in enumerate(pts)}
def B(x, y):
    t = add(add(mul(x[0], y[1]), neg(mul(x[1], y[0]))), add(mul(x[2], y[3]), neg(mul(x[3], y[2]))))
    return t
lines = set()
for i in range(n):
    for j in range(i + 1, n):
        p, r = pts[i], pts[j]
        if B(p, r) == ZERO:
            span = set()
            for a in range(q):
                for b in range(q):
                    if a or b:
                        v = tuple(add(mul(a, p[k]), mul(b, r[k])) for k in range(4))
                        span.add(idx[normalize(v)])
            lines.add(frozenset(span))
lines = sorted(lines, key=sorted)
assert len(lines) == n and all(len(L) == q + 1 for L in lines), len(lines)
inc = [[False]*n for _ in range(n)]
for l, L in enumerate(lines):
    for p in L: inc[p][l] = True
used = [set(l for l in range(n) if inc[p][l]) for p in range(n)]
matchings = []
def kuhn(adj):
    match_l = [-1]*n; match_p = [-1]*n
    sys.setrecursionlimit(10000)
    def try_(p, seen):
        for l in adj[p]:
            if l in seen: continue
            seen.add(l)
            if match_l[l] < 0 or try_(match_l[l], seen):
                match_l[l] = p; match_p[p] = l; return True
        return False
    for p in range(n):
        if not try_(p, set()): return None
    return [(p, match_p[p]) for p in range(n)]
for _ in range(extra):
    adj = []
    for p in range(n):
        a = [l for l in range(n) if l not in used[p]]
        rng.shuffle(a); adj.append(a)
    M = kuhn(adj); assert M is not None
    for p, l in M:
        used[p].add(l); matchings.append((p, l))
edges = [(p, n + l) for p in range(n) for l in range(n) if inc[p][l]] + [(p, n + l) for p, l in matchings]
with open(out, 'w') as f:
    f.write(f"{2*n} {len(edges)}\n")
    for u, v in edges: f.write(f"{u} {v}\n")
print("W(%d): base %d vertices, %d edges, degree %d" % (q, 2*n, len(edges), q + 1 + extra))
