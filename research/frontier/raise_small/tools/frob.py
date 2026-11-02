#!/usr/bin/env python3
"""frob.py Nlo Nhi [kmin] [--odd]: Frobenius groups Z_m x|_r Z_k with m prime, k | m - 1, r of order exactly k
(r = g^((m-1)/k) for a primitive root g), Nlo <= m k <= Nhi, k >= kmin (default 9). Prints "N m k r k 1" (glist format)."""
import sys

def isprime(n):
    if n < 2: return False
    i = 2
    while i * i <= n:
        if n % i == 0: return False
        i += 1
    return True

def primroot(p):
    fs, n, q = [], p - 1, 2
    while q * q <= n:
        if n % q == 0:
            fs.append(q)
            while n % q == 0: n //= q
        q += 1
    if n > 1: fs.append(n)
    for g in range(2, p):
        if all(pow(g, (p - 1) // f, p) != 1 for f in fs): return g

a = [x for x in sys.argv[1:] if not x.startswith('--')]
lo, hi = int(a[0]), int(a[1]); kmin = int(a[2]) if len(a) > 2 else 9; odd = '--odd' in sys.argv
out = []
for k in range(kmin, int(hi ** 0.5) + 2):
    if odd and k % 2 == 0: continue
    for m in range(max(3, lo // k), hi // k + 2):
        N = m * k
        if N < lo or N > hi or (m - 1) % k or not isprime(m): continue
        if odd and N % 2 == 0: continue
        g = primroot(m); out.append((N, m, k, pow(g, (m - 1) // k, m)))
for N, m, k, r in sorted(out):
    print(N, m, k, r, k, 1)
