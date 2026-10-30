#!/usr/bin/env python3
"""mk_base.py OUT M  : multiplicity matrix M (rows = side-0 vertices, cols = side-1) -> vl base file."""
import sys, json
out, M = sys.argv[1], json.loads(sys.argv[2])
k = len(M); assert all(len(r) == k for r in M)
E = []
for i in range(k):
    for j in range(k):
        E += [(i, k + j)] * M[i][j]
side = ['0'] * k + ['1'] * k
with open(out, 'w') as f:
    f.write(f"{2*k} {len(E)}\n" + " ".join(side) + "\n")
    for a, c in E: f.write(f"{a} {c}\n")
