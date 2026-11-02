#!/usr/bin/env python3
# Candidate metacyclic groups Z_m x|_r Z_k, N = m*k in [248522, 256000], k in [20,120], m prime, k | m-1, d = k (Frobenius).
import sys
from math import gcd
lo, hi = 248522, 256000
def isprime(n):
    if n < 2: return False
    i = 2
    while i * i <= n:
        if n % i == 0: return False
        i += 1
    return True
def factors(n):
    f, x, p = set(), n, 2
    while p * p <= x:
        while x % p == 0: f.add(p); x //= p
        p += 1
    if x > 1: f.add(x)
    return f
def primroot(m):
    fs = factors(m - 1)
    for g in range(2, m):
        if all(pow(g, (m - 1) // q, m) != 1 for q in fs): return g
res = []
for k in range(20, 121):
    for m in range((lo + k - 1) // k, hi // k + 1):
        N = m * k
        if N < lo or N > hi or (m - 1) % k: continue
        if not isprime(m): continue
        g = primroot(m)
        r = pow(g, (m - 1) // k, m)
        res.append((N, m, k, r))
res.sort()
for t in res: print(*t, 'd=k fpf=1')
print('count', len(res), file=sys.stderr)
