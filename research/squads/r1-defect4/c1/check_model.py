#!/usr/bin/env python3
"""Decode a kissat model of gen.build(k) and verify that it is a bipartite (k,3,-4)-graph (test helper only).
usage: check_model.py k model_output_file"""
import sys, itertools, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen import build

k = int(sys.argv[1])
vals = set()
for line in open(sys.argv[2]):
    if line.startswith('v'):
        vals.update(int(t) for t in line.split()[1:])
cnf, X, pool = build(k)
n = k * k - k - 1
M = [[1 if X[p, l] in vals else 0 for l in range(n)] for p in range(n)]
rows_ok = all(sum(r) == k for r in M) and all(sum(M[p][l] for p in range(n)) == k for l in range(n))
pts_ok = all(any(M[u][l] and M[v][l] for l in range(n)) for u, v in itertools.combinations(range(n), 2))
lines_ok = all(any(M[p][u] and M[p][v] for p in range(n)) for u, v in itertools.combinations(range(n), 2))
print(f'k={k} n={n} regular={rows_ok} points_share_line={pts_ok} lines_share_point={lines_ok} '
      f'valid={rows_ok and pts_ok and lines_ok}')
print('point0 lines:', [l for l in range(n) if M[0][l]])
