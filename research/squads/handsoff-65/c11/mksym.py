#!/usr/bin/env python3
"""Symmetric 2+2 base for swap symmetry sigma: A1<->B2, A2<->B1 (vertices 0=A1,1=A2 side 0; 2=B1,3=B2 side 1).
usage: mksym.py a pB pC BASE_OUT SYM_OUT
  base [[a,6-a],[6-a,a]]; classes A=(0,2)xa, B=(0,3)x(6-a), C=(1,2)x(6-a), D=(1,3)xa.
  sigma swaps A<->D (pairs, volt(D_j) = f(volt(A_j)) with f = inverse, theta = id) and maps B and C to themselves
  with an involution having pB (pC) pairs (rest fixed points). Fixed-point edges: volt in {g : g^2 = 1}.
  SYM_OUT lines: "ptype partner" per edge: ptype 0 = free rep with partner, 1 = partner (determined), 2 = self-fixed
  free rep (volt in F), 3 = tree (volt fixed 0). Edge order as in BASE_OUT."""
import sys
a, pB, pC = map(int, sys.argv[1:4]); bout, sout = sys.argv[4], sys.argv[5]
edges = []   # (u, w, ptype, partner)
idx = {}
def add_class(key, u, w, k):
    for j in range(k):
        idx[(key, j)] = len(edges); edges.append([u, w, None, None])
add_class('A', 0, 2, a); add_class('D', 1, 3, a)
add_class('B', 0, 3, 6 - a); add_class('C', 1, 2, 6 - a)
# A <-> D
for j in range(a):
    x, y = idx[('A', j)], idx[('D', j)]
    edges[x][2:] = [0, y]; edges[y][2:] = [1, x]
def selfclass(key, k, p):
    assert 2 * p <= k
    for j in range(p):
        x, y = idx[(key, 2 * j)], idx[(key, 2 * j + 1)]
        edges[x][2:] = [0, y]; edges[y][2:] = [1, x]
    for j in range(2 * p, k):
        e = idx[(key, j)]; edges[e][2:] = [2, -1]
selfclass('B', 6 - a, pB); selfclass('C', 6 - a, pC)
with open(bout, 'w') as f:
    f.write("SOL\n4 %d\n0 0 1 1\n" % len(edges))
    for u, w, _, _ in edges: f.write("%d %d 0\n" % (u, w))
with open(sout, 'w') as f:
    for _, _, t, p in edges: f.write("%d %d\n" % (t, p))
print("edges", len(edges), "reps", sum(1 for e in edges if e[2] in (0, 2)), "free-dim", sum(1 for e in edges if e[2] in (0, 2)))
