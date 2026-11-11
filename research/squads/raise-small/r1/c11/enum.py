#!/usr/bin/env python3
# enum.py LO HI: metacyclic (Z_m x|_r Z_k) x Z_c, m*k*c = N, nonabelian (d >= 2). Prints "N m k r c d".
import sys
from math import gcd
def mo(r, m):
    x, d = r % m, 1
    while x != 1 % m:
        x = x * r % m; d += 1
        if d > m: return 0
    return d
lo, hi = int(sys.argv[1]), int(sys.argv[2])
for N in range(lo, hi + 1):
    for c in range(1, N + 1):
        if N % c: continue
        M = N // c
        for k in range(2, M + 1):
            if M % k: continue
            m = M // k
            if m < 3: continue
            seen = set()
            for r in range(2, m):
                if gcd(r, m) != 1: continue
                d = mo(r, m)
                if d < 2 or k % d: continue
                sub = frozenset(pow(r, j, m) for j in range(d))
                if sub in seen: continue
                seen.add(sub)
                print(N, m, k, r, c, d)
