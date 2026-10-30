#!/usr/bin/env python3
# usage: mkbase.py OUT M  (M = symmetric-style 2x2 or 3x3 multiplicity matrix given as string "a,b;c,d")
import sys
out, mat = sys.argv[1], sys.argv[2]
rows = [list(map(int, r.split(','))) for r in mat.split(';')]
k = len(rows)
assert all(sum(r) == 7 for r in rows) and all(sum(rows[i][j] for i in range(k)) == 7 for j in range(k)), "not 7-regular"
E = [(i, k + j) for i in range(k) for j in range(k) for _ in range(rows[i][j])]
with open(out, 'w') as f:
    f.write(f"{2*k} {len(E)}\n" + " ".join(['0']*k + ['1']*k) + "\n")
    for a, c in E: f.write(f"{a} {c}\n")
print(out, "vertices", 2*k, "edges", len(E))
