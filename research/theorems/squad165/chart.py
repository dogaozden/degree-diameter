#!/usr/bin/env python3
"""Universal route charts over F_4^4 for the bipartite Haar-controller lift (see controller.py).
Unknowns: A_1..A_4 in GL_4(F_4), b_1..b_4 in F_4^4.  Lift: (g,x)_A ~ (s_i g, A_i x + lam b_i)_B.
A-side walk i1 i2 i3 i4 (consecutive distinct) is nonsingular iff U(i2;i1) + U(i3;i4) = F^4 (direct),
   U(j;i) = A_j^-1 span{b_i, b_j}.
B-side walk is nonsingular iff V(i2;i1) + V(i3;i4) = F^4,  V(j;i) = span{b_j, A_j A_i^-1 b_i}.
So: all 12 U(j;i) (and all 12 V(j;i)) 2-dimensional, U(j;i) cap U(k;l) = 0 whenever j != k (same for V).
Gauge: fiber coordinates on each side are free, so A_1 = I.  Search: random restarts + hill climbing on violations.
usage: python3 chart.py seconds seed  -> prints a chart with 0 violations (as integer lists) or the best found.
F_4 = {0,1,w,w^2} encoded 0,1,2,3 (a + b w -> a + 2b); addition is XOR.
"""
import sys, random, itertools, time
import numpy as np

MUL = [[0, 0, 0, 0], [0, 1, 2, 3], [0, 2, 3, 1], [0, 3, 1, 2]]
INV = [None, 1, 3, 2]

def mat_vec(A, v):
    out = []
    for r in range(4):
        s = 0
        for c in range(4):
            s ^= MUL[A[r][c]][v[c]]
        out.append(s)
    return tuple(out)

def mat_mul(A, B):
    return [[ (lambda r, c: __import__('functools').reduce(lambda x, y: x ^ y, [MUL[A[r][k]][B[k][c]] for k in range(4)]))(r, c)
              for c in range(4)] for r in range(4)]

def mat_inv(A):
    M = [list(A[r]) + [int(r == c) for c in range(4)] for r in range(4)]
    for col in range(4):
        piv = next((r for r in range(col, 4) if M[r][col]), None)
        if piv is None:
            return None
        M[col], M[piv] = M[piv], M[col]
        iv = INV[M[col][col]]
        M[col] = [MUL[iv][x] for x in M[col]]
        for r in range(4):
            if r != col and M[r][col]:
                f = M[r][col]
                M[r] = [x ^ MUL[f][y] for x, y in zip(M[r], M[col])]
    return [row[4:] for row in M]

def vid(v):
    return v[0] | (v[1] << 2) | (v[2] << 4) | (v[3] << 6)

# span masks of pairs: python int bitmask over 256 vectors
SCAL = list(range(4))
def span2(u, v):
    s = 0
    for a in SCAL:
        for b in SCAL:
            w = tuple(MUL[a][x] ^ MUL[b][y] for x, y in zip(u, v))
            s |= 1 << vid(w)
    return s

def violations(A, b):
    Ai = [mat_inv(M) for M in A]
    if any(x is None for x in Ai):
        return 10 ** 6
    bad = 0
    U = {}; V = {}
    for j in range(4):
        for i in range(4):
            if i == j: continue
            u = span2(mat_vec(Ai[j], b[i]), mat_vec(Ai[j], b[j]))
            v = span2(b[j], mat_vec(A[j], mat_vec(Ai[i], b[i])))
            U[(j, i)] = u; V[(j, i)] = v
            if bin(u).count('1') != 16: bad += 50
            if bin(v).count('1') != 16: bad += 50
    for (j, i), u in U.items():
        for (k, l), u2 in U.items():
            if j < k:
                if bin(u & u2).count('1') != 1: bad += 1
    for (j, i), v in V.items():
        for (k, l), v2 in V.items():
            if j < k:
                if bin(v & v2).count('1') != 1: bad += 1
    return bad

def rand_gl(rng):
    while True:
        A = [[rng.randrange(4) for _ in range(4)] for _ in range(4)]
        if mat_inv(A) is not None:
            return A

def rand_vec(rng):
    while True:
        v = tuple(rng.randrange(4) for _ in range(4))
        if any(v): return v

def search(seconds, seed):
    rng = random.Random(seed)
    I4 = [[int(r == c) for c in range(4)] for r in range(4)]
    best = None
    t0 = time.time()
    while time.time() - t0 < seconds:
        A = [I4] + [rand_gl(rng) for _ in range(3)]
        b = [rand_vec(rng) for _ in range(4)]
        c = violations(A, b)
        stall = 0
        while stall < 400 and c > 0 and time.time() - t0 < seconds:
            A2 = [row[:] for row in A]; A2 = [ [r[:] for r in M] for M in A]; b2 = list(b)
            if rng.random() < 0.5:
                k = rng.randrange(1, 4); r_ = rng.randrange(4); c_ = rng.randrange(4)
                A2[k][r_][c_] = rng.randrange(4)
                if mat_inv(A2[k]) is None: continue
            else:
                k = rng.randrange(4); b2[k] = rand_vec(rng)
            c2 = violations(A2, b2)
            if c2 <= c:
                stall = 0 if c2 < c else stall + 1
                A, b, c = A2, b2, c2
            else:
                stall += 1
        if best is None or c < best[0]:
            best = (c, A, b)
            print('best', c, flush=True)
        if c == 0:
            break
    return best

if __name__ == '__main__':
    c, A, b = search(float(sys.argv[1]), int(sys.argv[2]))
    print('violations', c)
    print('A =', A)
    print('b =', [list(x) for x in b])
