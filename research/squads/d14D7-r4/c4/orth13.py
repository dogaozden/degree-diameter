#!/usr/bin/env python3
# r4 c4 (q = 13): isometries of V = {x4 = -11 x0} acting on E13 (elliptic section of H(13)'s quadric).
# Adapted from research/squads/d14D7-r3/c3/orth.py (q = 11). Coordinates of V: U = (x0,x1,x2,x3,x5,x6).
# B(u,w) = u^T M w with M[0,0] = -2C, M[1,4] = M[4,1] = M[2,5] = M[5,2] = 1, M[3,3] = -2, C = 11 (mod 13).
# Usage: orth13.py SECONDS SEED OUTDIR [TARGETS]   (TARGETS default 4,7,8,12,14; also writes the explicit
#        rotation of order 14 of the anisotropic plane (x0,x3), identity on (x1,x2,x5,x6), and its square of order 7)
import sys, time, math, os
from collections import Counter
import numpy as np
p = 13
C = 11
D = '/home/user/degree-diameter/research/cell147/data/'
rows = np.loadtxt(D + 'E13.map', dtype=np.int64)
pid = rows[:, 0].copy(); sline = rows[:, 1].copy()
X = rows[:, 2:9] % p
N = X.shape[0]
assert N == 30772, N
assert np.all(X[:, 4] == (-C * X[:, 0]) % p)
U = X[:, [0, 1, 2, 3, 5, 6]].copy()
Qv = (-C * U[:, 0] ** 2 + U[:, 1] * U[:, 4] + U[:, 2] * U[:, 5] - U[:, 3] ** 2) % p
assert np.all(Qv == 0)
M = np.zeros((6, 6), dtype=np.int64)
M[0, 0] = (-2 * C) % p; M[1, 4] = M[4, 1] = 1; M[2, 5] = M[5, 2] = 1; M[3, 3] = (-2) % p
HALF = pow(2, p - 2, p)                     # 1/2 mod 13 = 7
INV = np.array([0] + [pow(a, p - 2, p) for a in range(1, p)], dtype=np.int64)
PW = np.array([p ** i for i in range(6)], dtype=np.int64)

def normalize(A):
    A = A % p
    first = np.argmax(A != 0, axis=1)
    lead = A[np.arange(A.shape[0]), first]
    return (A * INV[lead][:, None]) % p

Un = normalize(U)
IDX = np.full(p ** 6, -1, dtype=np.int64)
IDX[Un @ PW] = np.arange(N)
assert np.all(IDX[Un @ PW] == np.arange(N)), "normalized U not unique"

def perm_of(g):
    """permutation of the points of E13 (row order of E13.map) induced by u -> g u."""
    IM = normalize((Un @ g.T) % p)
    perm = IDX[IM @ PW]
    assert np.all(perm >= 0), "image not on E"
    return perm

def refl(v):
    Mv = (M @ v) % p
    qv = int((v @ Mv) % p) * HALF % p          # Q(v) = B(v,v)/2
    assert qv != 0
    return (np.eye(6, dtype=np.int64) - np.outer(v, Mv) * INV[qv]) % p

def rand_elem(rng, k):
    g = np.eye(6, dtype=np.int64)
    for _ in range(k):
        while True:
            v = rng.integers(0, p, 6).astype(np.int64)
            if int((v @ M @ v) % p) != 0: break
        g = (g @ refl(v)) % p
    return g

def cycles(perm):
    seen = np.zeros(N, dtype=bool); out = []
    pl = perm.tolist()
    for i in range(N):
        if seen[i]: continue
        c = []; j = i
        while not seen[j]:
            seen[j] = True; c.append(j); j = pl[j]
        out.append(c)
    return out

def lcm(a, b): return a * b // math.gcd(a, b)

def pperm(perm, k):
    res = np.arange(N); base = perm.copy()
    while k:
        if k & 1: res = base[res]
        base = base[base]; k >>= 1
    return res

def profile(perm):
    return tuple(sorted(Counter(len(c) for c in cycles(perm)).items()))

def rotation_plane():
    """explicit R in SO(A), A = (x0,x3) with Gram [[M00,0],[0,M33]]: R^T M_A R = M_A, det R = 1; return R of order 14."""
    MA = np.array([[M[0, 0], M[0, 3]], [M[3, 0], M[3, 3]]], dtype=np.int64)
    best = None
    for a in range(p):
        for b in range(p):
            for c in range(p):
                for d in range(p):
                    R = np.array([[a, b], [c, d]], dtype=np.int64)
                    if (a * d - b * c) % p != 1: continue
                    if not np.all((R.T @ MA @ R) % p == MA): continue
                    # order of R
                    P_ = R.copy(); k = 1
                    while not np.all(P_ == np.eye(2, dtype=np.int64)):
                        P_ = (P_ @ R) % p; k += 1
                        if k > 50: break
                    if k == 14 and best is None: best = R
    assert best is not None
    return best

def embed(R):
    g = np.eye(6, dtype=np.int64)
    g[0, 0], g[0, 3], g[3, 0], g[3, 3] = R[0, 0], R[0, 1], R[1, 0], R[1, 1]
    return g

if __name__ == '__main__':
    secs = float(sys.argv[1]); seed = int(sys.argv[2]); outdir = sys.argv[3]
    targets = [int(t) for t in sys.argv[4].split(',')] if len(sys.argv) > 4 else [4, 7, 8, 12, 14]
    os.makedirs(outdir, exist_ok=True)
    KEEP = 3
    rng = np.random.default_rng(seed)
    # explicit rotation of order 14 (the secant-clique rotation) and its square (order 7)
    R = rotation_plane(); g14 = embed(R); assert np.all((g14.T @ M @ g14) % p == M)
    p14 = perm_of(g14); g7 = (g14 @ g14) % p; p7 = perm_of(g7)
    print("explicit rotation: R =", R.tolist(), "profile(order14)", profile(p14), "profile(order7)", profile(p7), flush=True)
    store = {d: {} for d in targets}
    t0 = time.time(); samples = 0
    while time.time() - t0 < secs:
        k = int(rng.integers(2, 13))
        g = rand_elem(rng, k)
        assert np.all((g.T @ M @ g) % p == M)
        perm = perm_of(g)
        cyc = cycles(perm)
        n = 1
        for c in cyc: n = lcm(n, len(c))
        samples += 1
        for d in targets:
            if n % d == 0 and len(store[d]) < KEEP:
                h = pperm(perm, n // d)
                fp = profile(h)
                if fp not in store[d]:
                    store[d][fp] = h
                    print(f"sample {samples}: projective order {n}, order-{d} element profile {fp[:6]}{'...' if len(fp) > 6 else ''}", flush=True)
    written = []
    for d in targets:
        for j, (fp, h) in enumerate(store[d].items()):
            fn = os.path.join(outdir, f"perm_o{d}_{j}.txt")
            with open(fn, 'w') as f:
                f.write('\n'.join(str(int(x)) for x in h) + '\n')
            written.append((fn, d, fp))
    for name, pm, d in [("rot14", p14, 14), ("rot7", p7, 7)]:
        fn = os.path.join(outdir, f"perm_{name}.txt")
        with open(fn, 'w') as f:
            f.write('\n'.join(str(int(x)) for x in pm) + '\n')
        written.append((fn, d, profile(pm)))
    for fn, d, fp in written:
        print("WROTE", fn, "order", d, "profile", fp[:8], flush=True)
    print("samples", samples, "files", len(written), flush=True)
