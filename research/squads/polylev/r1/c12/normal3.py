"""Find F in SL(3,8) with F g F^-1 = g^8 and F^3 = I, so that <g, F> (order 219) normalises the order-73 Singer group."""
import sys, itertools
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/polylev')
import numpy as np
from hexlib import Hex
from spreadpart import mat_pow
H = Hex('/home/user/degree-diameter/research/theorems/polylev/hex/hex_q8.bin')
g = np.loadtxt('S73.g', dtype=np.int64).reshape(3, 3)
I3 = np.eye(3, dtype=np.int64)
g8 = mat_pow(H, g, 8)
# linear system for F (9 unknowns, row-major): (F g - g8 F)_{ij} = 0
M = np.zeros((9, 9), dtype=np.int64)
for i in range(3):
    for j in range(3):
        r = 3 * i + j
        for a in range(3):
            for b in range(3):
                c = 0
                if i == a: c = H.ADD[c, g[b, j]]
                if b == j: c = H.ADD[c, H.NEG[g8[i, a]]]
                M[r, 3 * a + b] = c
# nullspace over GF(8) by Gaussian elimination
A = M.copy(); piv_cols = []; row = 0
for col in range(9):
    pr = next((r for r in range(row, 9) if A[r, col]), None)
    if pr is None: continue
    A[[row, pr]] = A[[pr, row]]
    s = H.INV[A[row, col]]; A[row] = H.MUL[s, A[row]]
    for r in range(9):
        if r != row and A[r, col]:
            f = H.NEG[A[r, col]]; A[r] = H.ADD[A[r], H.MUL[f, A[row]]]
    piv_cols.append(col); row += 1
free = [c for c in range(9) if c not in piv_cols]
basis = []
for fc in free:
    v = np.zeros(9, dtype=np.int64); v[fc] = 1
    for r, pc in enumerate(piv_cols):
        v[pc] = H.NEG[A[r, fc]]
    basis.append(v)
print('nullspace dim', len(basis), flush=True)
found = None
for coef in itertools.product(range(8), repeat=len(basis)):
    if not any(coef): continue
    v = np.zeros(9, dtype=np.int64)
    for c, b in zip(coef, basis):
        if c: v = H.ADD[v, H.MUL[c, b]]
    F = v.reshape(3, 3)
    if H.det3(F) != 1: continue
    F3 = mat_pow(H, F, 3)
    if not (F3 == I3).all(): continue
    if (mat_pow(H, F, 1) == I3).all(): continue
    print('found F order 3 in SL(3,8):', F.tolist(), flush=True)
    found = F; break
if found is None:
    print('no F'); sys.exit(1)
F = found
np.savetxt('S73F.f', F, fmt='%d')
# check normalisation
lhs = H.mat_mul(H.mat_mul(F, g), H.mat_inv(F))
print('F g F^-1 == g^8 :', (lhs == g8).all())
pmF = H.sl3_point_map(F); lmF = H.line_map(pmF)
pmG = np.fromfile('S73.pperm', dtype=np.int32).astype(np.int64)
lmG = np.fromfile('S73.lperm', dtype=np.int32).astype(np.int64)
# orbit of <g, F> on points and lines via union-find
def orbits(gens, n):
    parent = list(range(n))
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]; x = parent[x]
        return x
    for p in gens:
        for x in range(n):
            a, b = find(x), find(int(p[x]))
            if a != b: parent[a] = b
    roots = np.array([find(x) for x in range(n)])
    _, lab = np.unique(roots, return_inverse=True)
    return lab
from collections import Counter
po = orbits([pmG, pmF], H.N)
lo = orbits([lmG, lmF], H.L)
print('G-point orbits', Counter(Counter(po.tolist()).values()), 'count', po.max() + 1)
print('G-line orbits', Counter(Counter(lo.tolist()).values()), 'count', lo.max() + 1)
po.astype(np.int32).tofile('G219.porb'); lo.astype(np.int32).tofile('G219.lorb')
pmF.astype(np.int32).tofile('S73F.pperm'); lmF.astype(np.int32).tofile('S73F.lperm')
