#!/usr/bin/env python3
"""normz.py: elements of SL(3,11) normalising <g> (g = the order-133 collineation), then merges RH with their images."""
import sys, itertools, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/c157b-r1/shared'); sys.path.insert(0, '/home/user/degree-diameter/research/squads/c157b-r1/c8')
from gperm import perm_from_mat7, sl3_to_mat7
import kmerge as K
p = 11
G = np.array([[8,1,10],[0,8,1],[7,4,4]], dtype=np.int64) % p
def mpow(M, e):
    R = np.eye(3, dtype=np.int64)
    for _ in range(e): R = (R @ M) % p
    return R
G11 = mpow(G, 11)
# linear system for F with F G = G11 F  (row-major vec)
A = np.zeros((9, 9), dtype=np.int64)
for i in range(3):
    for j in range(3):
        r = 3 * i + j
        for k in range(3):
            A[r, 3 * i + k] += G[k, j]          # (F G)_{ij}
            A[r, 3 * k + j] -= G11[i, k]        # (G11 F)_{ij}
A %= p
def nullspace_mod(A, p):
    A = A.copy() % p; m, n = A.shape; piv = []; r = 0
    for c in range(n):
        pr = next((i for i in range(r, m) if A[i, c] % p), None)
        if pr is None: continue
        A[[r, pr]] = A[[pr, r]]
        A[r] = (A[r] * pow(int(A[r, c]), p - 2, p)) % p
        for i in range(m):
            if i != r and A[i, c]: A[i] = (A[i] - A[i, c] * A[r]) % p
        piv.append(c); r += 1
        if r == m: break
    free = [c for c in range(n) if c not in piv]
    basis = []
    for f in free:
        v = np.zeros(n, dtype=np.int64); v[f] = 1
        for i, c in enumerate(piv): v[c] = (-A[i, f]) % p
        basis.append(v)
    return basis
NS = nullspace_mod(A, p)
print('intertwiner space dim', len(NS), flush=True)
rng = np.random.default_rng(5)
found = []
for trial in range(400):
    coef = rng.integers(0, p, size=len(NS))
    v = sum(c * b for c, b in zip(coef, NS)) % p
    F = v.reshape(3, 3)
    d = int(round(np.linalg.det(F.astype(float)))) % p
    if d == 0: continue
    for lam in range(1, p):
        if (pow(lam, 3, p) * d) % p == 1:
            s = (lam * F) % p
            break
    else:
        continue
    assert ((s @ G - G11 @ s) % p == 0).all()
    assert round(np.linalg.det(s.astype(float))) % p == 1
    found.append(s)
    if len(found) >= 6: break
print('normalising SL3 elements found:', len(found), flush=True)
def key(M): return tuple(M.reshape(-1))
orb = {key(np.eye(3, dtype=np.int64))}
# order of s modulo scalars: report
for s in found[:3]:
    o = 1; M = s.copy()
    while not (M % p == np.eye(3, dtype=np.int64)).all():
        M = (M @ s) % p; o += 1
        if o > 5000: break
    print('order of s in SL3:', o, flush=True)
RH = K.read_ids('/home/user/degree-diameter/research/squads/c157b-r1/shared/RH.txt')
inR = np.zeros(K.N, bool); inR[RH] = True
np.save('/home/user/degree-diameter/research/squads/c157b-r1/c8/normz_mats.npy', np.array(found))
best = (-1, None)
for idx, s in enumerate(found):
    pp, lp = perm_from_mat7(sl3_to_mat7(s))
    h = pp[RH]
    ov = int(inR[h].sum())
    res, gain = K.merge(RH, h, verbose=False)
    print(f'elt {idx}: overlap with RH {ov}, merged size {len(res)} (gain {gain})', flush=True)
    if gain > best[0]:
        best = (gain, res)
if best[1] is not None:
    with open('/home/user/degree-diameter/research/squads/c157b-r1/c8/merge_normz_best.txt', 'w') as f:
        f.write('\n'.join(map(str, best[1].tolist())) + '\n')
print('best gain', best[0])
