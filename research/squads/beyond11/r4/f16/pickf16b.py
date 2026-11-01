#!/usr/bin/env python3
# pickf16b.py d D Nlo Nhi nmax: SL(2,p) x Z_n with n composite (all prime factors = 1 mod 3), gcd(p,n)=1, N in [Nlo,Nhi]; prints mu.
import math, sys
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
    m = n; f = 2
    while f * f <= m:
        while m % f == 0:
            if f % 3 != 1: return False
            m //= f
        f += 1
    return m == 1 or m % 3 == 1
d, D = int(sys.argv[1]), int(sys.argv[2]); Nlo, Nhi = float(sys.argv[3]), float(sys.argv[4]); nmax = int(sys.argv[5])
w = W(d, D); out = []
ns = [n for n in range(4, nmax + 1) if ok_n(n) and not isprime(n)]
for p in range(5, 400):
    if not isprime(p): continue
    for n in ns:
        if math.gcd(p, n) != 1: continue
        N = p * (p * p - 1) * n
        if Nlo <= N <= Nhi:
            out.append((N, p, n, N * math.exp(-w / N)))
out.sort()
for N, p, n, mu in out: print(f"sl {p} x Z_{n} N={N} vertices={2*N} mu={mu:.2f}")
