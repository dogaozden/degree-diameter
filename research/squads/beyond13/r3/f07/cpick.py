#!/usr/bin/env python3
"""cpick.py k Nlo Nhi: odd composite k; prints m k r N with m prime, k | m-1, r of exact order k mod m."""
import sys
def isp(x):
    if x < 2: return False
    i = 2
    while i * i <= x:
        if x % i == 0: return False
        i += 1
    return True
def prim_root(m):
    fac = []; n = m - 1; p = 2
    while p * p <= n:
        if n % p == 0:
            fac.append(p)
            while n % p == 0: n //= p
        p += 1
    if n > 1: fac.append(n)
    for g in range(2, m):
        if all(pow(g, (m - 1) // q, m) != 1 for q in fac): return g
k, lo, hi = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
m = (lo // k) + 1
out = []
while m * k <= hi:
    if m * k >= lo and isp(m) and (m - 1) % k == 0:
        g = prim_root(m)
        r = pow(g, (m - 1) // k, m)
        out.append((m * k, m, r))
        if len(out) >= 4: break
    m += 1
for N, m, r in out: print(m, k, r, N)
