#!/usr/bin/env python3
# enum.py d D Nlo Nhi kmin kmax : metacyclic Z_m x|_r Z_k (any m, one r per (m,k) of exact order k, r != 1), N = m k in range
import sys, math
from math import gcd
d, D, lo, hi, kmin, kmax = map(int, sys.argv[1:7])
def W(d, D):
    if D % 2 == 0: return sum(d * (d - 1) ** (2 * i) for i in range(D // 2))
    return 1 + sum(d * (d - 1) ** (2 * i - 1) for i in range(1, (D - 1) // 2 + 1))
w = W(d, D)
rows = []
for k in range(kmin, kmax + 1):
    if not all(k % p for p in range(2, int(k ** .5) + 1)): pass  # any k
    for m in range((lo + k - 1) // k, hi // k + 1):
        if m < 3 or gcd(m, k) != 1 and False: continue
        # find r with r^k = 1 mod m, r != 1, gcd(r,m)=1, order exactly k (prime k) or any
        r = None
        for c in range(2, m):
            if gcd(c, m) != 1: continue
            if pow(c, k, m) == 1 and pow(c, 1, m) != 1:
                r = c; break
        if r is None: continue
        N = m * k
        rows.append((N * math.exp(-w / N), m, k, r, N))
rows.sort()
for mu, m, k, r, N in rows[:int(sys.argv[7]) if len(sys.argv) > 7 else 40]:
    print(m, k, r, N, f"{mu:.2f}")
