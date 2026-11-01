#!/usr/bin/env python3
"""mpick.py d D Nlo Nhi [k1,k2,..]: odd-order Frobenius groups Z_m x|_r Z_k (m prime = 1 mod k, k odd prime, r of order
k) with Nlo <= N = m k <= Nhi; prints "m k r N mu" (mu = size-law N exp(-W/N))."""
import sys, math
def W(d, D):
    if D % 2 == 0: return sum(d * (d - 1) ** (2 * i) for i in range(D // 2))
    return 1 + sum(d * (d - 1) ** (2 * i - 1) for i in range(1, (D - 1) // 2 + 1))
def isp(x):
    if x < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if x % p == 0: return x == p
    dd, s = x - 1, 0
    while dd % 2 == 0: dd //= 2; s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        y = pow(a, dd, x)
        if y in (1, x - 1): continue
        for _ in range(s - 1):
            y = y * y % x
            if y == x - 1: break
        else: return False
    return True
d, D, lo, hi = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3]), float(sys.argv[4])
ks = [int(x) for x in sys.argv[5].split(',')] if len(sys.argv) > 5 else [13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61]
w = W(d, D)
for k in ks:
    m0 = int(lo // k); m0 -= m0 % (2 * k); m = m0 + 1
    found = 0
    while m * k <= hi and found < 3:
        if m * k >= lo and isp(m):
            g = 2
            while True:
                r = pow(g, (m - 1) // k, m)
                if r != 1: break
                g += 1
            N = m * k; print(m, k, r, N, f"{N*math.exp(-w/N):.2f}"); found += 1
        m += 2 * k
