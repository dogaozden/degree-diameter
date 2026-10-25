#!/usr/bin/env python3
# Builds collineations of H(11) for the c4 groups (point permutations via shared/gperm.py).
import sys, os, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/c157b-r1/shared')
import gperm
q = 11
def mm(A, B): return (np.asarray(A, dtype=np.int64) @ np.asarray(B, dtype=np.int64)) % q
def mpow(A, k):
    R = np.eye(A.shape[0], dtype=np.int64); B = np.asarray(A, dtype=np.int64) % q
    while k:
        if k & 1: R = mm(R, B)
        B = mm(B, B); k >>= 1
    return R
def order(A, maxo=5000):
    A = np.asarray(A, dtype=np.int64) % q; I = np.eye(A.shape[0], dtype=np.int64); P = A.copy(); k = 1
    while not np.array_equal(P, I):
        P = mm(P, A); k += 1
        if k > maxo: return None
    return k
def det3(A):
    A = np.asarray(A, dtype=np.int64)
    return int(round(np.linalg.det(A))) % q
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
G = np.array([[8, 1, 10], [0, 8, 1], [7, 4, 4]], dtype=np.int64)
out = {}
out['g133'] = G
print('order g133', order(G))
# order-3 normaliser element: h G = G^11 h  (Frobenius on F_1331)
Gp = mpow(G, 11)
Lm = np.kron(np.eye(3, dtype=np.int64), G.T) - np.kron(Gp, np.eye(3, dtype=np.int64))
B = nullspace_mod(Lm, q)
rng = np.random.default_rng(1); h = None
for _ in range(2000):
    c = rng.integers(0, q, size=len(B)); v = sum(int(ci) * b for ci, b in zip(c, B)) % q
    H = v.reshape(3, 3)
    d = det3(H)
    if d == 0: continue
    s = next(s for s in range(1, q) if pow(s, 3, q) * d % q == 1)  # scale so det = 1
    h = (H * s) % q; break
assert h is not None and np.array_equal(mm(h, G), mm(Gp, h)) and det3(h) == 1
print('h order', order(h), 'h^3 in <g>?', any(np.array_equal(mpow(G, k), mpow(h, 3)) for k in range(133)))
out['h399'] = h
# order 120 element of GL(2,11) (primitive element of F_121), block diag(A, det(A)^-1)
def ord2(a, b, c, d):
    P = (1, 0, 0, 1); k = 0; cur = (a % q, b % q, c % q, d % q)
    A = cur; P = A; k = 1
    while P != (1, 0, 0, 1):
        P = ((P[0]*A[0]+P[1]*A[2]) % q, (P[0]*A[1]+P[1]*A[3]) % q, (P[2]*A[0]+P[3]*A[2]) % q, (P[2]*A[1]+P[3]*A[3]) % q)
        k += 1
        if k > 200: return None
    return k
A2 = None
for a in range(q):
    for b in range(q):
        for c in range(q):
            for d in range(q):
                if (a*d-b*c) % q and ord2(a, b, c, d) == 120: A2 = (a, b, c, d); break
            if A2: break
        if A2: break
    if A2: break
a, b, c, d = A2; detA = (a*d-b*c) % q; di = pow(detA, q-2, q)
g120 = np.zeros((3, 3), dtype=np.int64); g120[:2, :2] = [[a, b], [c, d]]; g120[2, 2] = di
print('g120 A2', A2, 'order', order(g120))
out['g120'] = g120
for k in (2, 3, 5, 10):
    out[f'g120p{k}'] = mpow(g120, k)
out['m110'] = np.array([[2, 2, 0], [0, 2, 0], [0, 0, 3]], dtype=np.int64)
print('m110 order', order(out['m110']), 'det', det3(out['m110']))
out['d1'] = np.diag([2, 6, 1]).astype(np.int64); out['d2'] = np.diag([1, 2, 6]).astype(np.int64)
out['u'] = np.array([[1, 1, 0], [0, 1, 0], [0, 0, 1]], dtype=np.int64)
# check g^{-T} in <g> (does the swap normalise the Singer group?)
gi_T = np.array(np.round(np.linalg.inv(G.astype(float)) * np.linalg.det(G.astype(float))), dtype=np.int64) # adj(G)
gi_T = (np.array(gi_T.T) * pow(det3(G), q-2, q)) % q
print('g^-T in <g>:', any(np.array_equal(mpow(G, k), gi_T) for k in range(133)))
for name, M in out.items():
    pp, lp = gperm.perm_from_mat7(gperm.sl3_to_mat7(M))
    np.savetxt(f'/home/user/degree-diameter/research/squads/c157b-r1/c4/perm_{name}.txt', pp, fmt='%d')
    print(name, 'cycles', gperm.orbit_sizes(pp))
# swap sigma: (v,a,w) -> (w,-a,v)
S7 = np.zeros((7, 7), dtype=np.int64)
for i in range(3): S7[i, 4+i] = 1; S7[4+i, i] = 1
S7[3, 3] = q - 1
pp, lp = gperm.perm_from_mat7(S7)
np.savetxt('/home/user/degree-diameter/research/squads/c157b-r1/c4/perm_sigma.txt', pp, fmt='%d')
print('sigma cycles', gperm.orbit_sizes(pp))
