#!/usr/bin/env python3
"""Solve the quotient form (A only, or with signs) for k and print structure relative to vertex 0."""
import sys, itertools
import numpy as np
from pysat.solvers import Cadical153
from enc_quot import build
k = int(sys.argv[1]); signs = '--signs' in sys.argv
cnf, pool, a = build(k, signs=signs, sym=True)
s = Cadical153(bootstrap_with=cnf.clauses)
print('solve:', s.solve())
mdl = set(l for l in s.get_model() if l > 0)
m = k * (k - 1) // 2; g = k - 2
A = np.zeros((m, m), dtype=int)
for (c, d), v in a.items():
    if v in mdl: A[c, d] = 1
O = list(range(1, g + 1)); I = list(range(g + 1, 2 * g + 1)); R = list(range(2 * g + 1, m))
print('row sums', set(A.sum(1)), 'col sums', set(A.sum(0)))
M = 2 * np.eye(m, dtype=int) + A
print('MM^T == kI+2J:', np.array_equal(M @ M.T, k * np.eye(m, dtype=int) + 2), ' M^TM:', np.array_equal(M.T @ M, k * np.eye(m, dtype=int) + 2))
blocks = {'0': [0], 'O': O, 'I': I, 'R': R}
for X in blocks:
    print(X, ' '.join(f'{Y}:{A[np.ix_(blocks[X], blocks[Y])].sum()}' for Y in blocks))
ev = np.linalg.eigvals(A)
print('eigenvalues |l+2|^2:', sorted(set(np.round(np.abs(ev + 2) ** 2, 6))))
G = A + A.T
print('undirected eigenvalues:', sorted(set(np.round(np.linalg.eigvalsh(G), 4))))
tri = np.trace(A @ A @ A) // 3
print('directed triangles:', tri)
np.save(sys.argv[2] if len(sys.argv) > 2 and not sys.argv[2].startswith('--') else f'A_k{k}.npy', A)
