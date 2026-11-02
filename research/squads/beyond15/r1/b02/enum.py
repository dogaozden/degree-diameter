#!/usr/bin/env python3
# enum.py d D Nlo Nhi kmin : metacyclic Z_m x|_r Z_k with Nlo<=m*k<=Nhi, k>=kmin, r of exact order k mod m.
# prints "N m k r mu" sorted by mu descending (mu = N exp(-W/N), W from mpick.py).
import sys, math, random
from math import gcd
def W(d, D):
    if D % 2 == 0: return sum(d * (d - 1) ** (2 * i) for i in range(D // 2))
    return 1 + sum(d * (d - 1) ** (2 * i - 1) for i in range(1, (D - 1) // 2 + 1))
def primes_of(n):
    ps = []; x = n; p = 2
    while p * p <= x:
        if x % p == 0:
            ps.append(p)
            while x % p == 0: x //= p
        p += 1
    if x > 1: ps.append(x)
    return ps
d, D, lo, hi, kmin = map(int, sys.argv[1:6])
w = W(d, D)
rng = random.Random(1)
out = []
pf_cache = {}
for k in range(kmin, hi // 2 + 1):
    pk = primes_of(k)
    mlo = max(3, -(-lo // k)); mhi = hi // k
    for m in range(mlo, mhi + 1):
        if gcd(m, k) == 0: pass
        # need a unit of exact order k mod m; quick filter: k | phi(m)
        phi = m
        for p in primes_of(m): phi = phi // p * (p - 1)
        if phi % k: continue
        found = None
        for _ in range(400):
            r = rng.randrange(2, m) if m > 2 else 1
            if gcd(r, m) != 1: continue
            if pow(r, k, m) != 1: continue
            if all(pow(r, k // p, m) != 1 for p in pk):
                found = r; break
        if found is None: continue
        N = m * k
        out.append((math.exp(-w / N) * N, N, m, k, found))
out.sort(reverse=True)
for mu, N, m, k, r in out:
    print(N, m, k, r, round(mu, 2))
