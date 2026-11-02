#!/usr/bin/env python3
"""pickg.py Nlo Nhi: metacyclic Frobenius groups Z_m x|_r Z_k (m prime, k | m-1, r of order k mod m), N = m k in [Nlo, Nhi].
Prints m k r N."""
import sys
def isprime(n):
    if n < 2: return False
    i = 2
    while i * i <= n:
        if n % i == 0: return False
        i += 1
    return True
lo, hi = int(sys.argv[1]), int(sys.argv[2])
for k in range(7, 400):
    for m in range(2 * k + 1, hi // k + 2):
        if m * k < lo or m * k > hi: continue
        if (m - 1) % k or not isprime(m): continue
        for r in range(2, m):
            if pow(r, k, m) == 1 and all(pow(r, d, m) != 1 for d in range(1, k) if k % d == 0):
                print(m, k, r, m * k); break
