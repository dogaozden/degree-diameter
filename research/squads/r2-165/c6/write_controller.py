#!/usr/bin/env python3
"""Write the controller edge list of a Haar controller H(G,S) with colour c relabelled to letter p[c].
usage: write_controller.py TABLE "s0 s1 s2 s3" "p0 p1 p2 p3" OUT.edges   (lines "a b c": A-vertex g, B-vertex s_c*g)"""
import sys
tab = open(sys.argv[1]).read().split()
m = int(tab[0]); T = list(map(int, tab[1:1 + m * m]))
S = list(map(int, sys.argv[2].split())); p = list(map(int, sys.argv[3].split()))
with open(sys.argv[4], 'w') as f:
    for g in range(m):
        for c in range(4):
            f.write(f"{g} {T[S[c] * m + g]} {p[c]}\n")
print('wrote', 4 * m, 'controller edges, m =', m)
