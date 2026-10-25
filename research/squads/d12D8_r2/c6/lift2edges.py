"""Expand an affcheck-format base file into the full lift edge list (vertex count, then 'a b' lines) for apsp/eccs.
Point (p,x) -> p*m+x; line (l,y) -> (NP+l)*m+y. usage: lift2edges.py BASE OUT"""
import sys
base, out = sys.argv[1], sys.argv[2]
with open(base) as f:
    NP, NL, m, _ = f.readline().split()
    NP, NL, m = int(NP), int(NL), int(m)
    edges = [tuple(map(int, line.split())) for line in f if line.strip()]
with open(out, 'w') as g:
    g.write(f"{(NP + NL) * m}\n")
    for p, l, a, b in edges:
        for x in range(m):
            g.write(f"{p*m + x} {(NP + l)*m + (a*x + b) % m}\n")
