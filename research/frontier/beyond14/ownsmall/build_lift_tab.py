#!/usr/bin/env python3
"""build_lift_tab.py SOL TABLEFILE OUT: edge list of the regular voltage lift in a salift .sol/.best file ("N id p ..."
then 3p lines "u v a") over the group with that id in TABLEFILE (own-small format: "G N id name" + N rows; written by
mktab.py). Vertex (u,g) -> u*N + g; base edge (u,v,a) gives (u,g) ~ (v, g*a). Writes "n" then "u v" lines.
Check the result with research/frontier/beyond14/bin/apsp OUT 3 14 (all pairs, independent of this script)."""
import sys
sol, tab, out = sys.argv[1], sys.argv[2], sys.argv[3]
L = [l.split() for l in open(sol) if l.strip()]
N, gid, p = int(L[0][0]), int(L[0][1]), int(L[0][2])
E = [(int(a), int(b), int(c)) for a, b, c in L[1:1 + 3 * p]]
T = None
with open(tab) as f:
    while True:
        h = f.readline()
        if not h: break
        t = h.split(); n_, id_ = int(t[1]), int(t[2])
        rows = [f.readline() for _ in range(n_)]
        if n_ == N and id_ == gid: T = [list(map(int, r.split())) for r in rows]; break
assert T is not None, "group not found"
edges = set()
for u, v, a in E:
    assert u < p <= v < 2 * p
    for g in range(N): edges.add((u * N + g, v * N + T[g][a]))
with open(out, 'w') as f:
    f.write(f"{2 * p * N}\n")
    for x, y in sorted(edges): f.write(f"{x} {y}\n")
print(f"n={2 * p * N} edges={len(edges)} (expected {3 * p * N})")
