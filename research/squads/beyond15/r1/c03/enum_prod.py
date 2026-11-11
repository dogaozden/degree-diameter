#!/usr/bin/env python3
"""enum_prod.py lo hi: pairs of odd-order Frobenius groups Z_m x|_r Z_k (k odd prime >= 5, m prime = 1 mod k) with
product order N = |G1||G2| in [lo, hi] for d=5, D=15. Prints "N mu m1 k1 r1 N1 m2 k2 r2 N2" (mu = N exp(-W/N))."""
import sys, math, bisect
def isp(x):
    if x < 2: return False
    i = 2
    while i * i <= x:
        if x % i == 0: return False
        i += 1
    return True
def W(d, D):
    if D % 2 == 0: return sum(d * (d - 1) ** (2 * i) for i in range(D // 2))
    return 1 + sum(d * (d - 1) ** (2 * i - 1) for i in range(1, (D - 1) // 2 + 1))
lo, hi = int(sys.argv[1]), int(sys.argv[2])
d, D = 5, 15
w = W(d, D)
def prim_root_order(m, k):
    for g in range(2, m):
        r = pow(g, (m - 1) // k, m)
        if r != 1: return r
groups = []
for k in [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]:
    m = 2 * k + 1
    while m * k <= hi // 55:
        if isp(m):
            groups.append((m * k, m, k, prim_root_order(m, k)))
        m += 2 * k
groups.sort()
NS = [g[0] for g in groups]
out = []
for i, (N1, m1, k1, r1) in enumerate(groups):
    jlo = bisect.bisect_left(NS, max(lo // N1, N1 if False else 1))
    jhi = bisect.bisect_right(NS, hi // N1)
    for j in range(max(jlo, i), jhi):
        N2, m2, k2, r2 = groups[j]
        N = N1 * N2
        if lo <= N <= hi:
            out.append((N, m1, k1, r1, N1, m2, k2, r2, N2))
out.sort()
for row in out:
    N = row[0]
    print(N, f"{N*math.exp(-w/N):.2f}", row[1], row[2], row[3], row[4], row[5], row[6], row[7], row[8])
print("count", len(out), "W", w, "groups", len(groups), file=sys.stderr)
