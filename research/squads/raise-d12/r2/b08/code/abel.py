# Abelian-quotient wall for Haar graphs H(G,S), D = 12 (odd walk lengths <= 11).
# S = {e} + (f-1) alpha-fixed letters + one alpha-orbit of size k (z-values w_i = r^i mod n, letters with z=0 for fixed/e).
# A B-vertex within distance 11 of (e,A) has image in Z_n equal to sum_i u_i w_i, where c in Z^Delta (signed letter counts),
# sum c = 1, ||c||_1 <= 11. Zero-z letters (e and f-1 fixed letters) absorb the rest of the sum.
# Coverage cov(x) = #{c : sum_i u_i w_i = x} (distinct signed-count patterns = lattice points), R = #{x : cov(x) >= 1}.
import sys, math
import numpy as np
from functools import lru_cache

D = 11  # max walk length (odd) for D = 12

def enum_u(k, R=D):
    # all u in Z^k with ||u||_1 <= R, as arrays
    out = []
    def rec(i, cur, rem):
        if i == k:
            out.append(tuple(cur)); return
        for x in range(-rem, rem + 1):
            cur.append(x); rec(i + 1, cur, rem - abs(x)); cur.pop()
    rec(0, [], R)
    return np.array(out, dtype=np.int64)

def zero_gen(f, R=D):
    # P[c][s] = #{v in Z^f : ||v||_1 = c, sum v = s}, c in 0..R, s in -R..R (index s+R)
    P = np.zeros((R + 1, 2 * R + 1), dtype=object)
    P[0][R] = 1
    for _ in range(f):
        Q = np.zeros_like(P)
        for c in range(R + 1):
            for si in range(2 * R + 1):
                v = P[c][si]
                if v == 0: continue
                for x in range(-R, R + 1):
                    c2 = c + abs(x)
                    if c2 > R: continue
                    s2 = si + x
                    if 0 <= s2 <= 2 * R:
                        Q[c2][s2] += v
        P = Q
    # G[b][t] = #{v : ||v|| <= b, sum v = t}
    G = np.zeros((R + 1, 2 * R + 1), dtype=object)
    for b in range(R + 1):
        acc = P[0:b + 1].sum(axis=0) if b >= 0 else 0
        G[b] = acc
    return G

def total_count(k, f):
    U = enum_u(k)
    G = zero_gen(f)
    norms = np.abs(U).sum(axis=1); sums = U.sum(axis=1)
    tot = 0
    for u_n, u_s in zip(norms, sums):
        b = D - u_n; t = 1 - u_s
        if b < 0 or abs(t) > D: continue
        tot += int(G[b][t + D])
    return tot

def coverage(n, r, k, f, U=None, G=None):
    if U is None: U = enum_u(k)
    if G is None: G = zero_gen(f)
    w = np.array([pow(r, i, n) for i in range(k)], dtype=np.int64)
    norms = np.abs(U).sum(axis=1); sums = U.sum(axis=1)
    b = D - norms; t = 1 - sums
    ok = (b >= 0) & (np.abs(t) <= D)
    # weight table lookup: G[b][t+D]
    bb = np.clip(b, 0, D); tt = np.clip(t + D, 0, 2 * D)
    wt = np.array([[float(G[i][j]) for j in range(2 * D + 1)] for i in range(D + 1)])[bb, tt]
    wt = np.where(ok, wt, 0.0)
    res = (U @ w) % n
    cov = np.bincount(res, weights=wt, minlength=n)
    return cov

def primes_upto(N):
    s = bytearray([1]) * (N + 1); s[0:2] = b'\x00\x00'
    for i in range(2, int(N ** 0.5) + 1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(N + 1) if s[i]]

def orders_k(n, k):
    # elements r in Z_n^* with r^k = 1, r != 1 (n prime, k prime): y = x^((n-1)/k) with y != 1, then y^j
    for x in range(2, n):
        y = pow(x, (n - 1) // k, n)
        if y != 1:
            return [pow(y, j, n) for j in range(1, k)]
    return []

if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'check':
        for k, f, n in [(3,1,73),(3,2,1063),(5,1,151),(5,2,941),(7,1,71),(5,5,271)]:
            U = enum_u(k); G = zero_gen(f)
            best = None
            for r in orders_k(n, k):
                cov = coverage(n, r, k, f, U, G)
                R = int((cov >= 1).sum())
                mn = cov.min(); mean = cov.mean()
                print(f"k={k} Delta={k+f} f={f} n={n} r={r}: R={R} of {n} ({100*R/n:.1f}%), min cov={mn:.0f}, mean={mean:.1f}")
