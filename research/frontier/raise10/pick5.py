#!/usr/bin/env python3
"""pick5.py d mu_lo mu_hi [k] [pmin pmax] [fam]: D = 10 groups PSL/SL(2,p) x Z_n with k | p-1 or p+1 (element of
projective order k), every prime factor of n = 1 mod k (or n = 1), size-law mu = N exp(-W/N) in [mu_lo, mu_hi]."""
import math, sys
def W(d, D=10): return sum(d * (d - 1) ** (2 * i) for i in range(D // 2))
def isprime(x):
    if x < 2: return False
    i = 2
    while i * i <= x:
        if x % i == 0: return False
        i += 1
    return True
def okn(n, k):
    if n == 1: return True
    m = n; q = 2
    while q * q <= m:
        if m % q == 0:
            if q % k != 1: return False
            while m % q == 0: m //= q
        q += 1
    return m == 1 or m % k == 1
a = sys.argv
d, lo, hi = int(a[1]), float(a[2]), float(a[3]); k = int(a[4]) if len(a) > 4 else 5
pmin = int(a[5]) if len(a) > 5 else 100; pmax = int(a[6]) if len(a) > 6 else 700; fams = a[7].split(',') if len(a) > 7 else ['psl']
w = W(d); out = []
for p in range(pmin, pmax + 1):
    if not isprime(p) or ((p - 1) % k and (p + 1) % k): continue
    for fam in fams:
        base = p * (p * p - 1) // (2 if fam == 'psl' else 1)
        for n in range(1, 100000):
            N = base * n
            mu = N * math.exp(-w / N)
            if mu > hi: break
            if mu < lo or math.gcd(n, p) != 1 or not okn(n, k): continue
            out.append((N, fam, p, n, mu))
out.sort()
for N, fam, p, n, mu in out: print(f"{fam} {p} {n} N={N} 2N={2*N} mu={mu:.2f} mem={N/2/1e9:.2f}GB")
