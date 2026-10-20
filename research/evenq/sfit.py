"""Quadratic forms R on Pi (X3 eliminated) with R/N constant on every line of S, N = d X2^2 + X2X5 + X5^2.
Uses only the Hermitian spread S (H(q)-lines inside Pi), computed locally: the S-line through X in Pi is pi_X cap Pi.
python3 sfit.py q delta"""
import itertools, sys
import numpy as np
from hexq import Field, _tr2, PAIRS
q, d = int(sys.argv[1]), int(sys.argv[2])
F = Field(q); ADD, MUL, INV = F.ADD, F.MUL, F.INV
assert _tr2(F, d) == 1
POW = q ** np.arange(7, dtype=np.int64)
# points of Pi cap Q: coordinates X0,X1,X2,X4,X5,X6 free, X3 = X0 + d X4; Q = X0X4+X1X5+X2X6+X3^2 = 0
grid = np.array(list(itertools.product(range(q), repeat=6)), dtype=np.int64)
X = np.zeros((len(grid), 7), np.int64)
X[:, [0, 1, 2, 4, 5, 6]] = grid
X[:, 3] = ADD[X[:, 0], MUL[d, X[:, 4]]]
Qv = ADD[ADD[MUL[X[:, 0], X[:, 4]], MUL[X[:, 1], X[:, 5]]], ADD[MUL[X[:, 2], X[:, 6]], MUL[X[:, 3], X[:, 3]]]]
X = X[(Qv == 0) & (grid.any(axis=1))]
first = np.argmax(X != 0, axis=1)
X = X[X[np.arange(len(X)), first] == 1]  # projective representatives
codes = X @ POW
o = np.argsort(codes); X, codes = X[o], codes[o]
print('Pi points', len(X), 'expect', (q**3 + 1) * (q + 1))
onv = (X[:, [0, 2, 3, 4, 5]] == 0).all(axis=1)
# S-line through each point: kernel of Tits rows of X restricted to Pi, i.e. y with M(X) y = 0 and y in Pi
def tits(x):
    M = np.zeros((8, 7), np.int64)
    for r, ((i, j), (k, l)) in enumerate(PAIRS):
        M[r, j] ^= x[i]; M[r, i] ^= x[j]; M[r, l] ^= x[k]; M[r, k] ^= x[l]
    M[6] = [x[4], x[5], x[6], 0, x[0], x[1], x[2]]
    M[7] = [1, 0, 0, 1, d, 0, 0]
    return M
def nullspace(M):
    M = M.copy(); piv, r = [], 0
    for c in range(7):
        nz = np.nonzero(M[r:, c])[0]
        if len(nz) == 0: continue
        i = r + nz[0]; M[[r, i]] = M[[i, r]]; M[r] = MUL[M[r], INV[M[r, c]]]
        f = M[:, c].copy(); f[r] = 0; rr = np.nonzero(f)[0]
        if len(rr): M[rr] = ADD[M[rr], MUL[f[rr][:, None], M[r][None, :]]]
        piv.append(c); r += 1
        if r == M.shape[0]: break
    out = []
    for fc in [c for c in range(7) if c not in piv]:
        y = np.zeros(7, np.int64); y[fc] = 1
        for i, pc in enumerate(piv): y[pc] = M[i, fc]
        out.append(y)
    return out
VARS = [0, 1, 2, 4, 5, 6]
MON = list(itertools.combinations_with_replacement(VARS, 2))
keep = [k for k, (i, j) in enumerate(MON) if (i, j) not in ((2, 2), (2, 5), (5, 5))]
def mon(x): return np.array([MUL[x[i], x[j]] for i, j in MON])[keep]
def Nf(x): return int(ADD[ADD[MUL[d, MUL[x[2], x[2]]], MUL[x[2], x[5]]], MUL[x[5], x[5]]])
rows = []
rng = np.random.default_rng(0)
idx = [i for i in rng.permutation(len(X)) if not onv[i]][:400]
for i in idx:
    x = X[i]
    B = nullspace(tits(x))
    assert len(B) == 2, len(B)
    y = B[0] if np.any(MUL[B[0], 1] != MUL[x, 1]) else B[1]
    # another point on the line: x + y (if y not prop. to x)
    for u in B:
        cand = u
        if np.linalg.matrix_rank(np.stack([x, cand]).astype(float)) == 2: break
    w = ADD[x, cand]
    # unknowns: R coefficients (keep) and constant k:  R(x) N(w) + R(w) N(x) = 0  (constancy of R/N)
    Nx, Nw = Nf(x), Nf(w)
    rows.append(ADD[MUL[mon(x), Nw], MUL[mon(w), Nx]])
M = np.array(rows)
ns = nullspace.__wrapped__(M) if hasattr(nullspace, '__wrapped__') else None
# general nullspace (more columns than 7)
def nullspace_g(M):
    M = M.copy(); piv, r = [], 0
    for c in range(M.shape[1]):
        nz = np.nonzero(M[r:, c])[0]
        if len(nz) == 0: continue
        i = r + nz[0]; M[[r, i]] = M[[i, r]]; M[r] = MUL[M[r], INV[M[r, c]]]
        f = M[:, c].copy(); f[r] = 0; rr = np.nonzero(f)[0]
        if len(rr): M[rr] = ADD[M[rr], MUL[f[rr][:, None], M[r][None, :]]]
        piv.append(c); r += 1
        if r == M.shape[0]: break
    out = []
    for fc in [c for c in range(M.shape[1]) if c not in piv]:
        y = np.zeros(M.shape[1], np.int64); y[fc] = 1
        for i, pc in enumerate(piv): y[pc] = M[i, fc]
        out.append(y)
    return out
for y in nullspace_g(M):
    print({f'X{MON[keep[k]][0]}X{MON[keep[k]][1]}': int(y[k]) for k in range(len(keep)) if y[k]})
