#!/usr/bin/env python3
# pickc.py d D mu_lo mu_hi [maxN]: SL/PSL(2,p) x Z_n with n = 1 or any n whose prime factors are all = 1 mod 3
# (composite allowed, e.g. 49, 91), gcd(p,n)=1. Size law as pick.py. Sorted by N.
import math, sys
from functools import lru_cache
def W(d, D):
    if D % 2 == 0: return sum(d * (d - 1) ** (2 * i) for i in range(D // 2))
    return 1 + sum(d * (d - 1) ** (2 * i - 1) for i in range(1, (D - 1) // 2 + 1))
def isprime(x):
    if x < 2: return False
    i = 2
    while i * i <= x:
        if x % i == 0: return False
        i += 1
    return True
def ok_n(n):
    if n == 1: return True
    m = n
    f = 2
    while f * f <= m:
        while m % f == 0:
            if f % 3 != 1: return False
            m //= f
        f += 1
    if m > 1 and m % 3 != 1: return False
    return True
d, D, lo, hi = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3]), float(sys.argv[4])
maxN = float(sys.argv[5]) if len(sys.argv) > 5 else 8.5e8
w = W(d, D); out = []
ns = [n for n in range(1, 3000) if ok_n(n)]
for p in range(5, 3000):
    if not isprime(p): continue
    for fam, base in (("sl", p * (p * p - 1)), ("psl", p * (p * p - 1) // 2)):
        for n in ns:
            N = base * n
            if N > maxN: break
            if math.gcd(p, n) != 1: continue
            mu = N * math.exp(-w / N)
            if lo <= mu <= hi: out.append((N, fam, p, n, mu))
out.sort()
for N, fam, p, n, mu in out: print(f"{fam} {p} {n} N={N} vertices={2*N} mu={mu:.2f}")
