"""Bipartite double of a gencheck-format affine product (e.g. mk_gstar.py output), as an explicit edge list for apsp.
usage: mk_bdouble.py IN.gen OUT.txt [double=1]   (double=0: write the product itself, non-bipartite)"""
import sys
f = open(sys.argv[1]); N, m = map(int, f.readline().split()); dbl = int(sys.argv[3]) if len(sys.argv) > 3 else 1
E = set()
for line in f:
    u, v, a, b = map(int, line.split())
    for x in range(m):
        y = (a * x + b) % m
        p, q = u * m + x, v * m + y
        if dbl:
            E.add((2 * p, 2 * q + 1)); E.add((2 * q, 2 * p + 1))
        elif p != q: E.add((min(p, q), max(p, q)))
nv = N * m * (2 if dbl else 1)
with open(sys.argv[2], 'w') as o:
    o.write(f"{nv}\n")
    for a, b in E: o.write(f"{a} {b}\n")
print(nv, len(E))
