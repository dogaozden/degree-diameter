#!/usr/bin/env python3
"""sol2edges.py SOL m k r [c] OUT: edge list of a salift_s / polish solution over G = (Z_m x|_r Z_k) x Z_c.

SOL: first line "N id p [cost]", then base edges "u v x" (x = element index ((a*k + j)*c + z), as gtab.py).
Lift: vertex (u, g) = u*N + idx(g); base edge (u, v, x) gives (u, g) ~ (v, g*x) for every g in G.
The product is recomputed here from (m, k, r, c) arithmetic, not read from a table, so this is a second implementation
of the group. Writes "n" then "u v" lines (apsp.c / score48 format) and prints n and the edge count.
"""
import sys

sol, m, k, r = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
c = int(sys.argv[5]) if len(sys.argv) > 6 else 1
out = sys.argv[-1]
lines = [l.split() for l in open(sol) if l.strip() and not l.startswith('#')]
N = int(lines[0][0]); assert N == m * k * c, (N, m, k, c)
base = [tuple(map(int, t[:3])) for t in lines[1:]]
dec = lambda x: (x // c // k, (x // c) % k, x % c)
enc = lambda a, j, z: (a * k + j) * c + z
def mul(g, h):
    a, j, z = dec(g); b, l, w = dec(h)
    return enc((a + pow(r, j, m) * b) % m, (j + l) % k, (z + w) % c)
nb = 1 + max(max(u, v) for u, v, _ in base)
E = set()
for (u, v, x) in base:
    for g in range(N):
        a, b = u * N + g, v * N + mul(g, x)
        E.add((min(a, b), max(a, b)))
with open(out, 'w') as f:
    f.write(f"{nb * N}\n")
    for a, b in sorted(E): f.write(f"{a} {b}\n")
print(nb * N, "vertices", len(E), "edges", "(expected", 3 * len(base) // 3 * N, ")")
