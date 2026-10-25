# Find sigma in GL(3,13) with S*Mg = Mg^13 * S (Frobenius of the Singer torus containing Mg), build its
# collineation (v,a,w) -> (S v, a, S^-T w) on points and lines, and check it normalises h.
import numpy as np, sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d16D7_r2/c8')
from load import *
from geo import build_PL
q = 13
Mg = np.array([[5,2,0],[12,5,2],[12,0,5]], dtype=np.int64)
def mpow(A, e):
    R = np.eye(3, dtype=np.int64); B = A.copy()
    while e:
        if e & 1: R = (R @ B) % q
        B = (B @ B) % q; e >>= 1
    return R
def inv(A):
    M = np.concatenate([A % q, np.eye(3, dtype=np.int64)], axis=1)
    for c in range(3):
        r = next(i for i in range(c, 3) if M[i, c] % q)
        M[[c, r]] = M[[r, c]]
        M[c] = (M[c] * pow(int(M[c, c]), q - 2, q)) % q
        for i in range(3):
            if i != c and M[i, c]: M[i] = (M[i] - M[i, c] * M[c]) % q
    return M[:, 3:]
def det(A):
    return int(round(np.linalg.det(A))) % q  # small ints ok
# linear system: S*Mg - Mg13*S = 0, unknown S (9 entries, row-major)
Mt = mpow(Mg, 13)
rows = []
for i in range(3):
    for j in range(3):
        eq = np.zeros(9, dtype=np.int64)
        # (S Mg)_{ij} = sum_k S_{ik} Mg_{kj}
        for k in range(3): eq[3*i + k] += Mg[k, j]
        # (Mt S)_{ij} = sum_k Mt_{ik} S_{kj}
        for k in range(3): eq[3*k + j] -= Mt[i, k]
        rows.append(eq % q)
A = np.array(rows, dtype=np.int64) % q
# nullspace mod q by gaussian elimination
def nullspace_mod(A, q):
    A = A.copy() % q; m, n = A.shape; piv = []; r = 0
    for c in range(n):
        p = next((i for i in range(r, m) if A[i, c] % q), None)
        if p is None: continue
        A[[r, p]] = A[[p, r]]
        A[r] = (A[r] * pow(int(A[r, c]), q - 2, q)) % q
        for i in range(m):
            if i != r and A[i, c]: A[i] = (A[i] - A[i, c] * A[r]) % q
        piv.append(c); r += 1
        if r == m: break
    free = [c for c in range(n) if c not in piv]
    basis = []
    for f in free:
        v = np.zeros(n, dtype=np.int64); v[f] = 1
        for i, pc in enumerate(piv): v[pc] = (-A[i, f]) % q
        basis.append(v)
    return basis
B = nullspace_mod(A, q)
print('intertwiner space dim', len(B))
cands = []
import itertools
for coeffs in itertools.product(range(q), repeat=len(B)):
    if not any(coeffs): continue
    v = sum(c * b for c, b in zip(coeffs, B)) % q
    S = v.reshape(3, 3)
    if det(S) % q != 0:
        cands.append(S)
print('invertible intertwiners', len(cands))
np.save('sigma_cands.npy', np.array(cands))
