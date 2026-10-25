"""Hermitian-type spread of H(8): lines of H(8) inside a hyperplane n^perp with q^3+1 = 513 lines (GF(8) arithmetic as
hexgen2.c: bit vectors mod x^3+x+1).  usage: spread8.py HEX OUT"""
import sys, numpy as np
sys.path.insert(0, '../tools'); import hexlib
q, lines, coord = hexlib.load(sys.argv[1]); P = coord.astype(np.int64)
def mul(x, y):
    r = 0
    while y:
        if y & 1: r ^= x
        y >>= 1; x <<= 1
        if x & 8: x ^= 11
    return r
MT = np.array([[mul(x, y) for y in range(8)] for x in range(8)])
def Bvec(X, n):   # alternating polar form in characteristic 2 (no x3 term)
    s = np.zeros(len(X), np.int64)
    for i, j in [(0, 4), (4, 0), (1, 5), (5, 1), (2, 6), (6, 2)]: s ^= MT[X[:, i], n[j]]
    return s
for c in range(1, 8):
    for n in [(1, 0, 0, 0, c, 0, 0), (1, 0, 0, 1, c, 0, 0)]:
        inp = Bvec(P, n) == 0
        sp = np.nonzero(inp[lines].all(axis=1))[0]
        print(n, 'points', inp.sum(), 'lines inside', len(sp))
        if len(sp) == q ** 3 + 1:
            open(sys.argv[2], 'w').write(f'# {len(sp)} lines of H(8) inside n^perp, n = {n}\n' + '\n'.join(map(str, sp.tolist())) + '\n'); sys.exit(0)
