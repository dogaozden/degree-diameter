import sys
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d14D7-r3/c3')
from orth import *
h = np.load(sys.argv[1]) if len(sys.argv) > 1 else np.load('h240.npy')
I = np.eye(6, dtype=np.int64)
def mpow(A, k):
    R = I.copy(); B = A.copy()
    while k:
        if k & 1: R = (R @ B) % p
        B = (B @ B) % p; k >>= 1
    return R
def rank(A):
    A = A.copy() % p; r = 0
    for c in range(A.shape[1]):
        piv = next((i for i in range(r, A.shape[0]) if A[i, c]), None)
        if piv is None: continue
        A[[r, piv]] = A[[piv, r]]; A[r] = (A[r] * INV[A[r, c]]) % p
        for i in range(A.shape[0]):
            if i != r and A[i, c]: A[i] = (A[i] - A[i, c] * A[r]) % p
        r += 1
    return r
# isometry up to scalar? h^T M h = mu M
G = (h.T @ M @ h) % p
mu = G[1, 4] * INV[M[1, 4]] % p
print("h^T M h = mu M with mu =", mu, np.array_equal(G, (mu * M) % p))
for k in range(1, 9):
    hk = mpow(h, k)
    if np.array_equal(hk, (hk[0, 0] * I) % p) and hk[0,0]: print("h^%d = %d I" % (k, hk[0, 0])); break
# char poly via Faddeev-LeVerrier is messy mod p; use brute: det(xI - h) at x = 0..10 and interpolate
def det(A):
    A = A.copy() % p; n = A.shape[0]; d = 1
    for c in range(n):
        piv = next((i for i in range(c, n) if A[i, c]), None)
        if piv is None: return 0
        if piv != c: A[[c, piv]] = A[[piv, c]]; d = -d
        d = d * A[c, c] % p; inv = INV[A[c, c]]
        for i in range(c + 1, n):
            if A[i, c]: A[i] = (A[i] - A[i, c] * inv * A[c]) % p
    return d % p
vals = [det((x * I - h) % p) for x in range(p)]
print("det(xI - h) for x = 0..10:", vals)
for lam in range(1, p):
    print("lam", lam, "dims ker(h - lam) =", 6 - rank((h - lam * I) % p), " ker((h^2 - lam)) =", 6 - rank((mpow(h, 2) - lam * I) % p))
