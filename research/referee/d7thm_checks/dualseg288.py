#!/usr/bin/env python3
"""Remark (ii) of D7_THEOREMS.md §1.3: a dual segment set of 288 lines in H(4).  Reads the geometry and the line sets of
squad card conics2-r1/c8 (branch claude/conics-2-diameter-7-ic0oat), checks with own code that the geometry is a
generalized hexagon of order (4,4) (incidence-graph distance profile from every element) and that each set is a dual
segment set.  Usage: dualseg288.py geom_q4.txt set1 [set2 ...]"""
import sys
from hexlib import dist_array
import numpy as np
L = open(sys.argv[1]).read().split('\n')
q, n, nl = map(int, L[0].split())
lines = []
for l in L[1:]:
    if l.strip():
        lines.append(tuple(sorted(set(map(int, l.split())))))
lines = sorted(set(lines))
assert len(lines) == nl and all(len(x) == q + 1 for x in lines), (len(lines), nl)
adj = [[] for _ in range(n + nl)]
for i, x in enumerate(lines):
    for p in x: adj[p].append(n + i); adj[n + i].append(p)
exp = [1] + [(q + 1) * q**(i - 1) for i in range(1, 6)] + [q**5]
for s in range(n + nl):
    d = dist_array(adj, s)
    assert [int((d == i).sum()) for i in range(7)] == exp and (d >= 0).all()
print('geometry: %d points, %d lines, GH of order (%d,%d) (distance profile from every element)' % (n, nl, q, q))
# the set files index the lines in file order (as listed in geom); map file order -> our sorted order
fileorder = []
seen = set()
for l in L[1:]:
    if l.strip():
        t = tuple(sorted(map(int, l.split())))
        if t not in seen: seen.add(t); fileorder.append(t)
idx = {t: i for i, t in enumerate(fileorder)}
for fn in sys.argv[2:]:
    G = [fileorder[int(x)] for x in open(fn).read().split()]
    Gs = set(G); on = {}
    for x in G:
        for p in x: on.setdefault(p, []).append(x)
    ok = True
    for x in G:
        meet = {p for p in x if len(on[p]) > 1}
        if len(meet) > 1: ok = False
    print('%s: %d lines, dual segment set: %s' % (fn.split('/')[-1], len(Gs), ok))

# Is the geometry H(4) or its dual?  In H(q) every point is distance-2 regular (for x opposite y, z: if x^y and x^z,
# x^y = Gamma_2(x) cap Gamma_4(y), share two points they are equal); in the dual of H(q), q != 3^h, points are not.
# Test the first 40 points of the file, and of the referee's own H(4) (hexlib) on its points and on its lines.
import random
from hexlib import Hexagon
def regular_fraction(adjm, elems, tries=40):
    bad = 0
    random.seed(3)
    for x in elems[:tries]:
        d = dist_array(adjm, x); opp = [y for y in range(len(adjm)) if d[y] == 6]; g2 = set(np.where(d == 2)[0])
        traces = {}
        for y in random.sample(opp, 60):
            dy = dist_array(adjm, y); traces[y] = frozenset(p for p in g2 if dy[p] == 4)
        T = list(traces.values())
        for i in range(len(T)):
            for j in range(i + 1, len(T)):
                if len(T[i] & T[j]) >= 2 and T[i] != T[j]: bad += 1; break
    return bad
H = Hexagon(4); A = H.incidence_adj()
print('violations of distance-2 regularity (40 elements, 60 opposite elements each): file points %d; own H(4) points %d; own H(4) lines %d' % (
    regular_fraction(adj, list(range(n))), regular_fraction(A, list(range(H.N))), regular_fraction(A, list(range(H.N, 2 * H.N)))))
