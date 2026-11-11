#!/usr/bin/env python3
# enumerate odd-order metacyclic Z_m x|_r Z_k with N = m k in [lo,hi]; r of exact order k mod m (r != 1)
import sys, math
lo, hi = int(sys.argv[1]), int(sys.argv[2])
ks = [int(x) for x in sys.argv[3].split(',')]
def isprime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    i = 3
    while i * i <= x:
        if x % i == 0: return False
        i += 2
    return True
def factor(n):
    f = {}; p = 2
    while p * p <= n:
        while n % p == 0: f[p] = f.get(p, 0) + 1; n //= p
        p += 1
    if n > 1: f[n] = f.get(n, 0) + 1
    return f
def order_ok_r(m, k):
    # find r in (Z/m)^* with r^k = 1, r != 1 ; return smallest such r or None
    if m == 1: return None
    # random-ish scan: r = g^((phi/k)) for generators; simple scan over small r
    for r in range(2, min(m, 200000)):
        if math.gcd(r, m) != 1: continue
        if pow(r, k, m) == 1 and r != 1:
            return r
    return None
out = []
for k in ks:
    mlo, mhi = (lo + k - 1) // k, hi // k
    for m in range(mlo | 1, mhi + 1, 2):
        if math.gcd(m, k) != 1 and m % k == 0: continue
        if isprime(m):
            if (m - 1) % k: continue
        r = order_ok_r(m, k)
        if r is None: continue
        out.append((m * k, m, k, r))
out.sort()
for N, m, k, r in out: print(f"meta {m} {k} {r} N={N}")
