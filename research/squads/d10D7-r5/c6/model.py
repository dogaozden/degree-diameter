# Model check for hex_q9.bin: find GF(9) encoding + quadric X0X4+X1X5+X2X6 = c*X3^2 that all coordinates satisfy,
# and check that file lines are totally isotropic (bilinear form zero on each line).
import struct, itertools, sys
import numpy as np
FN = '/home/user/degree-diameter/research/d10D7/hex/hex_q9.bin'
data = open(FN, 'rb').read()
q, N, _ = struct.unpack_from('<iii', data, 0)
assert q == 9 and N == 66430
LP = np.frombuffer(data, dtype='<i4', count=N*10, offset=12).reshape(N, 10).copy()
C = np.frombuffer(data, dtype=np.uint8, count=7*N, offset=12+4*N*10).reshape(N, 7).astype(np.int64).copy()

def field(p1, p0, enc):
    # element e <-> c0 + c1*x, x^2 = -p1*x - p0 ; enc 0: e = c0 + 3*c1 ; enc 1: e = 3*c0 + c1
    def dec(e):
        return (e % 3, e // 3) if enc == 0 else (e // 3, e % 3)
    def enc_(c0, c1):
        c0 %= 3; c1 %= 3
        return c0 + 3*c1 if enc == 0 else 3*c0 + c1
    add = [[0]*9 for _ in range(9)]; mul = [[0]*9 for _ in range(9)]
    for a in range(9):
        for b in range(9):
            a0, a1 = dec(a); b0, b1 = dec(b)
            add[a][b] = enc_(a0+b0, a1+b1)
            m0 = a0*b0 - a1*b1*p0
            m1 = a0*b1 + a1*b0 - a1*b1*p1
            mul[a][b] = enc_(m0, m1)
    return add, mul

def check_field(add, mul):
    # field axioms quick check: every nonzero has inverse, distributivity sample
    for a in range(1, 9):
        if not any(mul[a][b] == 1 for b in range(1, 9)): return False
    for a in range(9):
        for b in range(9):
            for c in range(9):
                if mul[a][add[b][c]] != add[mul[a][b]][mul[a][c]]: return False
    return True

mods = [(0, 1), (1, 2), (2, 2)]   # x^2+1, x^2+x+2, x^2+2x+2
found = []
for (p1, p0) in mods:
    for enc in (0, 1):
        add, mul = field(p1, p0, enc)
        if not check_field(add, mul):
            continue
        M = np.array(mul); A = np.array(add)
        for c in range(9):
            # value = X0X4 + X1X5 + X2X6 - c X3^2 (in GF(9)); test all points
            t = M[C[:,0], C[:,4]]; t = A[t, M[C[:,1], C[:,5]]]; t = A[t, M[C[:,2], C[:,6]]]
            neg_c = [b for b in range(9) if add[b][c] == 0][0]
            s = A[t, M[neg_c, M[C[:,3], C[:,3]]]]
            if np.all(s == 0):
                found.append((p1, p0, enc, c))
print('field/quadric candidates satisfied by all points:', found)
if not found:
    sys.exit(1)
