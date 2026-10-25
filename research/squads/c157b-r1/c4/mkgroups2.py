#!/usr/bin/env python3
# extra c4 groups: monomial group of the torus (order 600), normaliser of C120 (order 240), sigma combinations
import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/c157b-r1/shared')
import gperm
q = 11; D = '/home/user/degree-diameter/research/squads/c157b-r1/c4/'
exec(open(D + 'mkgroups.py').read().split("G = np.array")[0].split("import gperm")[1].split("q = 11", 1)[1]) if False else None
def mm(A, B): return (np.asarray(A, dtype=np.int64) @ np.asarray(B, dtype=np.int64)) % q
def det3(A): return int(round(np.linalg.det(np.asarray(A, dtype=np.float64)))) % q
def nullspace_mod(M, p):
    M = np.array(M, dtype=np.int64) % p; rows, cols = M.shape; piv = []; r = 0
    for c in range(cols):
        pr = next((i for i in range(r, rows) if M[i, c] % p), None)
        if pr is None: continue
        M[[r, pr]] = M[[pr, r]]; M[r] = (M[r] * pow(int(M[r, c]), p - 2, p)) % p
        for i in range(rows):
            if i != r and M[i, c]: M[i] = (M[i] - M[i, c] * M[r]) % p
        piv.append(c); r += 1
        if r == rows: break
    basis = []
    for f in [c for c in range(cols) if c not in piv]:
        v = np.zeros(cols, dtype=np.int64); v[f] = 1
        for i, pc in enumerate(piv): v[pc] = (-M[i, f]) % p
        basis.append(v)
    return basis
def savep(name, M):
    pp, lp = gperm.perm_from_mat7(gperm.sl3_to_mat7(M))
    np.savetxt(D + f'perm_{name}.txt', pp, fmt='%d'); print(name, gperm.orbit_sizes(pp))
d1 = np.diag([2, 6, 1]).astype(np.int64); d2 = np.diag([1, 2, 6]).astype(np.int64)
P3 = np.array([[0, 0, 1], [1, 0, 0], [0, 1, 0]], dtype=np.int64)
T2 = np.array([[0, 1, 0], [1, 0, 0], [0, 0, -1]], dtype=np.int64) % q
savep('mono_d1', d1); savep('mono_d2', d2); savep('mono_P3', P3); savep('mono_T2', T2)
# normaliser of C120: h2 A = A^11 h2 on the GL(2,11) block, then block diag(h2, det(h2)^-1)
A = np.array([[0, 1], [3, 1]], dtype=np.int64)
Ap = np.eye(2, dtype=np.int64)
for _ in range(11): Ap = mm(Ap, A)
Lm = np.kron(np.eye(2, dtype=np.int64), A.T) - np.kron(Ap, np.eye(2, dtype=np.int64))
B = nullspace_mod(Lm, q); rng = np.random.default_rng(3); h2 = None
for _ in range(500):
    c = rng.integers(0, q, size=len(B)); H = (sum(int(ci) * b for ci, b in zip(c, B)) % q).reshape(2, 2)
    d = int(round(np.linalg.det(H))) % q
    if d: h2 = H; break
assert h2 is not None and np.array_equal(mm(h2, A), mm(Ap, h2))
g = np.zeros((3, 3), dtype=np.int64); g[:2, :2] = h2; g[2, 2] = pow(int(round(np.linalg.det(h2))) % q, q - 2, q)
print('h240 det', det3(g))
savep('h240', g)
# sigma and g120 generated group: check orbits later with orbmis
