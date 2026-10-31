#!/usr/bin/env python3
"""haar_table_edges.py EXPORT OUT.edges s_1 .. s_6: edge list of H(G,S) from a haarex-format export (n, then the n x n
table with identity 0, then automorphisms). Vertex g of side A = g, of side B = n + g; edge g -- n + s*g."""
import sys
t = open(sys.argv[1]).read().split(); n = int(t[0]); tab = t[1:1 + n * n]
S = [int(x) for x in sys.argv[3:]]
with open(sys.argv[2], "w") as f:
    f.write(f"{2 * n}\n")
    for g in range(n):
        for s in S: f.write(f"{g} {n + int(tab[s * n + g])}\n")
