#!/usr/bin/env python3
# pickf16.py d D mu_lo mu_hi: SL(2,p) x Z_n, n in {49, 91, 133} (composite, primes 1 mod 3), gcd(p,n)=1; size law as pick.py.
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
d, D, lo, hi = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3]), float(sys.argv[4])
w = W(d, D); out = []
for n in (49, 91, 133):
    for p in range(5, 3000):
        if not isprime(p) or math.gcd(p, n) != 1: continue
        N = p * (p * p - 1) * n
        mu = N * math.exp(-w / N)
        if lo <= mu <= hi: out.append((N, p, n, mu))
out.sort()
for N, p, n, mu in out: print(f"sl {p} x Z_{n} N={N} vertices={2*N} mu={mu:.2f}")
