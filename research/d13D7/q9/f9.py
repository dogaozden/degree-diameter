"""F_9 = F_3[al], al^2 = 2, element a + 3b (hexgen.c convention): tables and small linear algebra."""
import numpy as np
A = np.zeros((9, 9), np.int64); M = np.zeros((9, 9), np.int64)
for x in range(9):
    for y in range(9):
        a, b, c, d = x % 3, x // 3, y % 3, y // 3
        A[x, y] = (a + c) % 3 + 3 * ((b + d) % 3); M[x, y] = (a * c + 2 * b * d) % 3 + 3 * ((a * d + b * c) % 3)
NEG = np.array([[y for y in range(9) if A[x, y] == 0][0] for x in range(9)])
INV = np.array([0] + [[y for y in range(9) if M[x, y] == 1][0] for x in range(1, 9)])
FROB = np.array([M[x, M[x, x]] for x in range(9)])
def sub(x, y): return A[x, NEG[y]]
def matvec(Mat, v):
    out = np.zeros(Mat.shape[0], np.int64)
    for k in range(Mat.shape[1]): out = A[out, M[Mat[:, k], v[k]]]
    return out
def rref(Mat):
    """row-reduce a matrix over F_9; returns (R, pivots)"""
    R = Mat.copy() % 9; r = 0; piv = []
    rows, cols = R.shape
    for c in range(cols):
        s = next((i for i in range(r, rows) if R[i, c]), None)
        if s is None: continue
        R[[r, s]] = R[[s, r]]
        R[r] = M[INV[R[r, c]], R[r]]
        for i in range(rows):
            if i != r and R[i, c]:
                R[i] = A[R[i], NEG[M[R[i, c], R[r]]]]
        piv.append(c); r += 1
        if r == rows: break
    return R[:r], piv
def nullspace(Mat):
    R, piv = rref(Mat)
    cols = Mat.shape[1]; free = [c for c in range(cols) if c not in piv]; basis = []
    for f in free:
        v = np.zeros(cols, np.int64); v[f] = 1
        for i, p in enumerate(piv): v[p] = NEG[R[i, f]]
        basis.append(v)
    return np.array(basis, np.int64).reshape(len(basis), cols)
J = [(0, 4), (4, 0), (1, 5), (5, 1), (2, 6), (6, 2)]
def Bf(x, y):
    s = 0
    for i, j in J: s = A[s, M[x[i], y[j]]]
    return A[s, NEG[M[2, M[x[3], y[3]]]]]
def Qf(x):
    s = A[A[M[x[0], x[4]], M[x[1], x[5]]], M[x[2], x[6]]]
    return A[s, NEG[M[x[3], x[3]]]]
