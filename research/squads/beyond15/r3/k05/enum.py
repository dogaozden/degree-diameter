#!/usr/bin/env python3
"""enum.py Nlo Nhi kmin kmax: metacyclic Z_m x|_r Z_k, m COMPOSITE, m k = N in [Nlo, Nhi], one r per cyclic subgroup
<r> of (Z/m)^* with r^k = 1, r != 1 (order d | k). Prints "N m k r order fpf"."""
import sys
from math import gcd
lo, hi, kmin, kmax = map(int, sys.argv[1:5])
def isprime(x):
    return x > 1 and all(x % p for p in range(2, int(x**0.5) + 1))
for N in range(lo, hi + 1):
    for k in range(kmin, kmax + 1):
        if N % k: continue
        m = N // k
        if m < 4 or isprime(m): continue
        seen = set()
        for r in range(2, m):
            if gcd(r, m) != 1 or pow(r, k, m) != 1: continue
            sub = frozenset(pow(r, j, m) for j in range(k))
            if sub in seen: continue
            seen.add(sub)
            order = min(j for j in range(1, k + 1) if pow(r, j, m) == 1)
            fpf = int(all(gcd(pow(r, j, m) - 1, m) == 1 for j in range(1, order)))
            print(N, m, k, r, order, fpf)
