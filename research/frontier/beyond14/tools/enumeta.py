#!/usr/bin/env python3
"""enumeta.py Nlo Nhi [kmin]: metacyclic groups Z_m x|_r Z_k with Nlo <= m k <= Nhi, k >= kmin (12), one r of exact
multiplicative order k mod m per (m,k); prints "N m k r fpf" (fpf = 1 if r^j - 1 is a unit mod m for 0 < j < k)."""
import sys
from math import gcd
lo, hi = int(sys.argv[1]), int(sys.argv[2]); kmin = int(sys.argv[3]) if len(sys.argv) > 3 else 12
for N in range(lo, hi + 1):
    for k in range(kmin, N // 5 + 1):
        if N % k: continue
        m = N // k
        for r in range(2, m):
            if gcd(r, m) != 1 or pow(r, k, m) != 1 or any(pow(r, j, m) == 1 for j in range(1, k)): continue
            fpf = int(all(gcd(pow(r, j, m) - 1, m) == 1 for j in range(1, k)))
            print(N, m, k, r, fpf); break
