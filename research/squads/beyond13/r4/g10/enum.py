#!/usr/bin/env python3
# enum.py: list odd-order Frobenius factors Z_m x|_r Z_k (m prime, k odd prime, k | m-1) with N = m k in [lo, hi],
# then pairs (F1, F2) with N1*N2 in [Nlo, Nhi] and both k >= KMIN. Prints "N1*N2 | m1 k1 r1 | m2 k2 r2".
import sys
def isp(x):
    if x < 2: return False
    i = 2
    while i * i <= x:
        if x % i == 0: return False
        i += 1
    return True
def rootof(m, k):
    for g in range(2, m):
        r = pow(g, (m - 1) // k, m)
        if r != 1: return r
lo, hi = int(sys.argv[1]), int(sys.argv[2])     # factor size range
Nlo, Nhi = int(sys.argv[3]), int(sys.argv[4])   # product range
KMIN = int(sys.argv[5]) if len(sys.argv) > 5 else 7
F = []
for k in range(KMIN, 200):
    if not isp(k) or k % 2 == 0: continue
    for m in range(2 * k + 1, hi // k + 1, 2 * k):   # m = 1 mod 2k: odd and = 1 mod k
        if m * k < lo: continue
        if isp(m) and (m - 1) % k == 0:
            F.append((m * k, m, k, rootof(m, k)))
F.sort()
out = []
for a in F:
    for b in F:
        if a[0] > b[0]: continue
        N = a[0] * b[0]
        if Nlo <= N <= Nhi: out.append((N, a, b))
out.sort()
for N, a, b in out:
    print(f"{N} | {a[1]} {a[2]} {a[3]} | {b[1]} {b[2]} {b[3]}")
