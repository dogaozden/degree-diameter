#!/usr/bin/env python3
"""Lines of H(9) inside the hyperplane n^perp (Hermitian spread when n^perp meets Q(6,9) in an elliptic quadric).
usage: spread9.py HEX_Q9_BIN OUT_IDX"""
import sys, numpy as np, itertools
sys.path.insert(0, '../tools'); import hexlib
q, lines, coord = hexlib.load(sys.argv[1]); P = coord.astype(int)
A = np.zeros((9, 9), int); M = np.zeros((9, 9), int)
for x in range(9):
    for y in range(9):
        a, b, c, d = x % 3, x // 3, y % 3, y // 3
        A[x, y] = (a + c) % 3 + 3 * ((b + d) % 3); M[x, y] = (a * c + 2 * b * d) % 3 + 3 * ((a * d + b * c) % 3)
NEG = np.array([[y for y in range(9) if A[x, y] == 0][0] for x in range(9)])
def Bvec(X, n):
    s = np.zeros(len(X), int)
    for i, j in [(0, 4), (4, 0), (1, 5), (5, 1), (2, 6), (6, 2)]: s = A[s, M[X[:, i], n[j]]]
    return A[s, NEG[M[2, M[X[:, 3], n[3]]]]]
for n in [(1, 0, 0, 0, 1, 0, 0), (1, 0, 0, 0, 4, 0, 0), (1, 0, 0, 0, 5, 0, 0), (1, 0, 0, 0, 2, 0, 0)]:
    inperp = Bvec(P, np.array(n)) == 0
    sp = np.nonzero(inperp[lines].all(axis=1))[0]
    print('n =', n, 'points in n^perp:', inperp.sum(), 'lines inside:', len(sp))
    if len(sp) == q ** 3 + 1:
        open(sys.argv[2], 'w').write(f'# {len(sp)} lines of H(9) inside n^perp, n = {n}\n' + '\n'.join(map(str, sp.tolist())) + '\n')
        print('wrote', sys.argv[2]); break
