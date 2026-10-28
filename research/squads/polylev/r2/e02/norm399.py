"""Order-399 group: the order-133 Singer element g (S133) together with an element M of SL(3,11) normalising <g>
(M g M^-1 = g^11, Frobenius-type). Orbits of the generated group on points of H(11) are computed by union-find over
the point permutations of g and M; the orbit id of every point is written to TAG_porb.bin.
usage: norm399.py TAG"""
import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/polylev')
from hexlib import Hex
TAG = sys.argv[1]
out = '/home/user/degree-diameter/research/squads/polylev/r2/e02/'
p = 11
g = np.loadtxt(out + 'S133.g', dtype=np.int64).reshape(3, 3) % p
def mm(A, B): return (A @ B) % p
def mpow(A, e):
    R = np.eye(3, dtype=np.int64); Bm = A.copy()
    while e:
        if e & 1: R = mm(R, Bm)
        Bm = mm(Bm, Bm); e >>= 1
    return R
def det3(a):
    d = a[0,0]*(a[1,1]*a[2,2]-a[1,2]*a[2,1]) - a[0,1]*(a[1,0]*a[2,2]-a[1,2]*a[2,0]) + a[0,2]*(a[1,0]*a[2,1]-a[1,1]*a[2,0])
    return int(d) % p
gk = mpow(g, p)
print('det g', det3(g), 'g^133 == I:', np.array_equal(mpow(g, 133), np.eye(3, dtype=np.int64)), flush=True)
rows = []
for i in range(3):
    for l in range(3):
        row = np.zeros(9, dtype=np.int64)
        for j in range(3):
            row[i*3+j] = (row[i*3+j] + g[j, l]) % p
            row[j*3+l] = (row[j*3+l] - gk[i, j]) % p
        rows.append(row)
A = np.array(rows) % p
def nullspace_mod(A, p):
    A = A.copy() % p; m, n = A.shape; piv = []; r = 0
    for c in range(n):
        pr = next((i for i in range(r, m) if A[i, c]), None)
        if pr is None: continue
        A[[r, pr]] = A[[pr, r]]
        inv = pow(int(A[r, c]), p - 2, p); A[r] = (A[r] * inv) % p
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
B = nullspace_mod(A, p)
print('solution space dim', len(B), flush=True)
rng = np.random.default_rng(5)
M = None
for t in range(1000):
    coef = rng.integers(0, p, size=len(B))
    v = sum(int(c) * b for c, b in zip(coef, B)) % p
    Mc = v.reshape(3, 3)
    d = det3(Mc)
    if d == 0: continue
    c = next(c for c in range(1, p) if pow(c, 3, p) == pow(d, p - 2, p))
    M = (c * Mc) % p
    break
assert M is not None and det3(M) == 1
assert np.array_equal(mm(M, g), mm(gk, M)), 'not normalising'
print('M =', M.tolist(), flush=True)
H = Hex('/home/user/degree-diameter/research/theorems/polylev/hex/hex_q11.bin')
N = H.N
pm = np.asarray(H.sl3_point_map(M), dtype=np.int64)
pg = np.fromfile(out + 'S133.pperm', dtype=np.int32).astype(np.int64)
np.array(pm, dtype=np.int32).tofile(out + 'M11.pperm')
par = np.arange(N)
def find(x):
    while par[x] != x:
        par[x] = par[par[x]]; x = par[x]
    return x
for perm in (pg, pm):
    for x in range(N):
        a, b = find(x), find(int(perm[x]))
        if a != b: par[a] = b
roots = np.array([find(x) for x in range(N)])
uniq, orb = np.unique(roots, return_inverse=True)
sizes = np.bincount(orb)
print('group orbits', len(uniq), 'sizes', np.unique(sizes, return_counts=True), flush=True)
orb.astype(np.int32).tofile(out + TAG + '_porb.bin')
