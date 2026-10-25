"""Spread of H(8): the lines of H(8) inside a hyperplane x3 = a0 x0 + a4 x4 (not through the nucleus e3) that meets
Q(6,8) in an elliptic quadric; wants q^3+1 = 513 lines.  GF(8) as in hexgen2.c.  usage: spread8b.py HEX OUT"""
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
for a0 in range(8):
    for a4 in range(8):
        inh = (P[:, 3] == (MT[a0, P[:, 0]] ^ MT[a4, P[:, 4]]))
        sp = np.nonzero(inh[lines].all(axis=1))[0]
        if len(sp) == q ** 3 + 1:
            open(sys.argv[2], 'w').write(f'# {len(sp)} lines of H(8) inside x3 = {a0} x0 + {a4} x4 (GF(8) bit vectors mod x^3+x+1)\n' + '\n'.join(map(str, sp.tolist())) + '\n')
            print(f'a0={a0} a4={a4}: points {inh.sum()}, lines inside {len(sp)} -> {sys.argv[2]}'); sys.exit(0)
print('none found')
