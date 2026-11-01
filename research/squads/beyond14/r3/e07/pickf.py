#!/usr/bin/env python3
"""pickf.py Nlo Nhi kmin kmax: Frobenius groups Z_m x|_r Z_k, m prime, k | m-1, r of exact order k mod m.
Prints m k r N (one r per (m,k), smallest). Usage: pickf.py Nlo Nhi kmin kmax"""
import sys
def isprime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    i = 3
    while i * i <= n:
        if n % i == 0: return False
        i += 2
    return True
def primes_of(n):
    ps, d = [], 2
    while d * d <= n:
        if n % d == 0:
            ps.append(d)
            while n % d == 0: n //= d
        d += 1
    if n > 1: ps.append(n)
    return ps
lo, hi, kmin, kmax = map(int, sys.argv[1:5])
for k in range(kmin, kmax + 1):
    mlo = max(lo // k, 2)
    mhi = hi // k + 1
    # m ≡ 1 mod k
    m = mlo + ((1 - mlo) % k)
    while m <= mhi:
        if m * k >= lo and m * k <= hi and isprime(m):
            ps = primes_of(k)
            found = None
            for g in range(2, m):
                r = pow(g, (m - 1) // k, m)
                if r != 1 and all(pow(r, k // d, m) != 1 for d in ps):
                    found = r; break
            if found is not None:
                print(m, k, found, m * k)
        m += k
