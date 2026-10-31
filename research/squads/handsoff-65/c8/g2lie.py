# Lie structure of g2 over F5 inside gl7, root vectors via a split Cartan, root subgroups x_e(t)=1+te+t^2e^2/2
from lin import *
import sys
def vec(M): return [M[i][j] for i in range(N) for j in range(N)]
# coordinates: choose 14 independent coordinate positions
Gv = [vec(mat(v)) for v in G2basis]
def solve_coords(M):
    # find c with sum c_i Gv[i] = vec(M); Gv rows independent; use fixed pivot columns
    return COORD(vec(M))
# precompute pivot columns for coordinate extraction
def build_coord():
    rows = [r[:] for r in Gv]   # 14 x 49
    # gaussian elimination tracking combination: find 14 columns with invertible submatrix
    cols = []
    sub = []
    for c in range(N*N):
        cand = sub + [[r[c] for r in Gv]]
        # check rank of 14 x len(cols)+1 matrix (columns of Gv at chosen cols)
        M = [[Gv[i][cc] for cc in cols + [c]] for i in range(14)]
        if rank(M) == len(cols) + 1:
            cols.append(c)
        if len(cols) == 14: break
    A = [[Gv[i][cc] for cc in cols] for i in range(14)]  # 14x14, rows = basis elements
    # M = sum c_i Gv_i => at cols: vec(M)[cc] = sum_i c_i A[i][k]; solve c A = v
    Ainv = minv(A)  # A is 14x14 with rows basis; we need c = v * A^{-1} (row vector)
    return cols, Ainv
def rank(M):
    M = [r[:] for r in M]; r = 0
    if not M: return 0
    nc = len(M[0])
    for c in range(nc):
        pr = next((i for i in range(r, len(M)) if M[i][c] % p), None)
        if pr is None: continue
        M[r], M[pr] = M[pr], M[r]
        inv = pow(M[r][c], p-2, p); M[r] = [(x*inv) % p for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] % p:
                f = M[i][c]; M[i] = [(x - f*y) % p for x, y in zip(M[i], M[r])]
        r += 1
    return r
COLS, AINV = build_coord()
def coords(M):
    v = vec(M)
    w = [v[c] for c in COLS]  # w = c A
    # c = w * Ainv (row vector times matrix)
    return [sum(w[k]*AINV[k][j] for k in range(14)) % p for j in range(14)]
def bracket(X, Y):
    return madd(mm(X, Y), mm(Y, X), -1)
def adm(X):
    cols = []
    for i in range(14):
        Gi = mat(G2basis[i])
        cols.append(coords(bracket(X, Gi)))
    # matrix with column i = coords(ad X (G_i))
    return [[cols[j][i] for j in range(14)] for i in range(14)]
def nullsp(M):
    return nullspace(M, len(M[0]))
def lincomb(cs, mats):
    R = [[0]*N for _ in range(N)]
    for c, Mx in zip(cs, mats):
        if c: R = madd(R, [[c*x % p for x in r] for r in Mx])
    return R
