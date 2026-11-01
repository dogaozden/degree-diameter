#!/usr/bin/env python3
"""build_lift.py SOL m k r OUT: edge list of the regular voltage lift in a salift .sol file ("N id p" then 3p lines
"u v a") over G = Z_m x|_r Z_k, built from the group definition (not from a table): index a <-> (a // k, a % k),
(x,j)(y,l) = (x + r^j y mod m, j + l mod k). Vertex (u,g) -> u*N + g; base edge (u,v,a) gives (u,g) ~ (v, g*a).
Writes "n" then "u v" lines; prints n, edges and the number of distinct edges."""
import sys
sol, m, k, r, out = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
L = [l.split() for l in open(sol) if l.strip()]
N, gid, p = int(L[0][0]), int(L[0][1]), int(L[0][2]); assert N == m * k and pow(r, k, m) == 1
E = [(int(a), int(b), int(c)) for a, b, c in L[1:1 + 3 * p]]
R = [pow(r, j, m) for j in range(k)]
def mul(g, h):
    x, j = divmod(g, k); y, l = divmod(h, k)
    return ((x + R[j] * y) % m) * k + (j + l) % k
edges = set()
for u, v, a in E:
    assert u < p <= v < 2 * p
    for g in range(N): edges.add((u * N + g, v * N + mul(g, a)))
n = 2 * p * N
with open(out, 'w') as f:
    f.write(f"{n}\n")
    for x, y in sorted(edges): f.write(f"{x} {y}\n")
print(f"n={n} edges={len(edges)} (expected {3 * p * N})")
