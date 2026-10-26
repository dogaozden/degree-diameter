#!/usr/bin/env python3
"""PG(4,3) flag graph (type A4, q=3, I={2,4}, J={1,3}, identity double coset), built explicitly.
A side: flags L<S (line in solid), B side: flags P<Pi (point in plane). Adjacent iff P<L<Pi<S (a complete flag
refines both). 16-regular bipartite. Writes an apsp.c input edge list (first line n) to argv[1]."""
import sys, itertools
q, nd = 3, 5
def normalize(v):
    for x in v:
        if x:
            inv = 1 if x == 1 else 2
            return tuple((inv * y) % q for y in v)
    return None
vecs = [v for v in itertools.product(range(q), repeat=nd) if any(v)]
points = sorted({normalize(v) for v in vecs})
pidx = {p: i for i, p in enumerate(points)}
def rank_basis(pts):
    # greedy independent set among the given point indices (as vectors)
    basis = []
    for i in pts:
        cand = basis + [points[i]]
        if len(span_points(cand)) == (q ** len(cand) - 1) // (q - 1):
            basis = cand
    return basis
def span_points(basis):
    S = set()
    for coef in itertools.product(range(q), repeat=len(basis)):
        if any(coef):
            v = [0] * nd
            for c, b in zip(coef, basis):
                for k in range(nd):
                    v[k] = (v[k] + c * b[k]) % q
            if any(v):
                S.add(pidx[normalize(v)])
    return frozenset(S)
# subspaces by vector dimension: dim1 points, dim2 lines, dim3 planes, dim4 solids (as point sets)
lines = set()
for a, b in itertools.combinations(range(len(points)), 2):
    lines.add(span_points([points[a], points[b]]))
lines = sorted(lines, key=sorted)
planes = set()
for L in lines:
    Lb = rank_basis(sorted(L))
    for p in range(len(points)):
        if p not in L:
            planes.add(span_points(Lb + [points[p]]))
planes = sorted(planes, key=sorted)
solids = set()
for Pl in planes:
    pb = rank_basis(sorted(Pl))
    for p in range(len(points)):
        if p not in Pl:
            solids.add(span_points(pb + [points[p]]))
solids = sorted(solids, key=sorted)
print('points', len(points), 'lines', len(lines), 'planes', len(planes), 'solids', len(solids), file=sys.stderr)
A = [(L, S) for S in solids for L in lines if L <= S]
B = [(P, Pi) for Pi in planes for P in range(len(points)) if P in Pi]
Aidx = {x: i for i, x in enumerate(A)}
Bidx = {x: i + len(A) for i, x in enumerate(B)}
n = len(A) + len(B)
edges = set()
for (L, S) in A:
    for Pi in planes:
        if L <= Pi and Pi <= S:
            for P in L:
                edges.add((Aidx[(L, S)], Bidx[(P, Pi)]))
print('n', n, '|A|', len(A), '|B|', len(B), 'edges', len(edges), file=sys.stderr)
deg = [0] * n
for u, v in edges:
    deg[u] += 1; deg[v] += 1
print('degree min/max', min(deg), max(deg), file=sys.stderr)
with open(sys.argv[1], 'w') as f:
    f.write(f'{n}\n')
    for u, v in sorted(edges):
        f.write(f'{u} {v}\n')
