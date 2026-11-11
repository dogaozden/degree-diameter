#!/usr/bin/env python3
"""Bipartite double cover G x K2 of a graph given as an edge list ("u v" lines, 0-based; any other lines ignored):
vertices (x, 0) = x and (x, 1) = n + x, edges (x,0) -- (y,1) and (y,0) -- (x,1) for every edge xy.  Writes the apsp.c
format (first line = number of vertices).  G x K2 is bipartite and has the degrees of G; its diameter is <= D + 1 iff
every pair of vertices of G is joined by walks of both parities of length <= D + 1 (same side: even <= D ... ).
usage: python3 double_cover.py in.edges out.edges"""
import sys
E = []
for line in open(sys.argv[1]):
    p = line.split()
    if len(p) >= 2 and p[0].lstrip('-').isdigit() and p[1].lstrip('-').isdigit():
        E.append((int(p[0]), int(p[1])))
n = 1 + max(max(a, b) for a, b in E)
assert all(a != b for a, b in E), 'loop'
assert len({(min(a, b), max(a, b)) for a, b in E}) == len(E), 'repeated edge'
with open(sys.argv[2], 'w') as f:
    f.write(f"{2 * n}\n")
    for a, b in E:
        f.write(f"{a} {n + b}\n{b} {n + a}\n")
print('G: n', n, 'edges', len(E), '-> G x K2: n', 2 * n, 'edges', 2 * len(E))
