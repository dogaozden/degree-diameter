#!/usr/bin/env python3
# pick.py Nlo Nhi : metacyclic Z_m x|_r Z_k with m odd (composite allowed), r^k = 1 mod m, gcd(r,m)=1,
# N = m k in [Nlo, Nhi]. Prints "N m k r ord_r" sorted by N. Prefers r of full order k mod m.
import sys, math
from math import gcd
lo, hi = int(sys.argv[1]), int(sys.argv[2])
def order(r, m):
    x, o = r % m, 1
    while x != 1 % m:
        x = x * r % m; o += 1
        if o > 10**6: return None
    return o
out = []
for k in range(5, hi // 3 + 1):
    if k % 2 == 0 and k < 6: continue
    mlo = max(3, -(-lo // k)); mhi = hi // k
    for m in range(mlo | 1, mhi + 1, 2):
        if m % 3 == 0 and False: pass
        # r with r^k = 1 mod m: r in the subgroup of exponent dividing k; only test up to a few candidates
        cnt = 0
        for r in range(2, m - 1):
            if gcd(r, m) != 1: continue
            if pow(r, k, m) != 1: continue
            o = order(r, m)
            if o == k:
                out.append((m * k, m, k, r, o)); cnt += 1
                if cnt >= 1: break
        # (only one r per (m,k), to keep the list short)
out.sort()
for row in out: print(*row)
