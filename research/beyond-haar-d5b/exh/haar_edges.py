#!/usr/bin/env python3
"""Edge list of the Haar graph H(G, S) from a group table and a haar5x line "SOL S s0 s1 ...": vertices (g, A) = g,
(g, B) = m + g, edges (g, A) ~ (s g, B).  usage: haar_edges.py GROUP "SOL S ..." OUT.edges"""
import sys
f = open(sys.argv[1]).read().split(); m = int(f[0]); mul = [[int(f[1 + i * m + j]) for j in range(m)] for i in range(m)]
S = [int(t) for t in sys.argv[2].split()[2:]]
with open(sys.argv[3], 'w') as o:
    o.write(f"{2 * m}\n")
    for g in range(m):
        for s in S: o.write(f"{g} {m + mul[s][g]}\n")
