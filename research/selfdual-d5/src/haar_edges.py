#!/usr/bin/env python3
"""haar_edges.py G.ht OUT.edges s_1 .. s_K: edge list of the Haar graph H(G,S) from an export table
(vertex g of side A = g, of side B = n + g; edge g -- n + s g)."""
import sys
t = open(sys.argv[1]).read().split(); n = int(t[0]); tab = t[2:2 + n * n]
S = [int(x) for x in sys.argv[3:]]
with open(sys.argv[2], "w") as f:
    f.write(f"{2 * n}\n")
    for g in range(n):
        for s in S: f.write(f"{g} {n + int(tab[s * n + g])}\n")
