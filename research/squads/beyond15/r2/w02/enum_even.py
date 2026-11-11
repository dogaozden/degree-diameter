#!/usr/bin/env python3
# enumerate metacyclic Z_m x|_r Z_k with m EVEN, k in range, N=m*k in [lo,hi]; print m k r order_r N mu  (d=4 D=16 by default)
import sys, math
from math import gcd
d, D, lo, hi = int(sys.argv[1]), int(sys.argv[2]), int(float(sys.argv[3])), int(float(sys.argv[4]))
klo, khi = int(sys.argv[5]), int(sys.argv[6])
def W(d, D):
    if D % 2 == 0: return sum(d * (d - 1) ** (2 * i) for i in range(D // 2))
    return 1 + sum(d * (d - 1) ** (2 * i - 1) for i in range(1, (D - 1) // 2 + 1))
w = W(d, D)
def order(r, m):
    x, o = r % m, 1
    while x != 1 % m:
        x = x * r % m; o += 1
        if o > 10**7: return None
    return o
out = []
for k in range(klo, khi + 1):
    mlo = max(2, -(-lo // k)); mhi = hi // k
    for m in range(mlo + (mlo % 2), mhi + 1, 2):
        # r of multiplicative order dividing k in (Z/m)^*; search small r
        found = None
        for r in range(2, min(m, 2000)):
            if gcd(r, m) != 1: continue
            if pow(r, k, m) != 1 % m: continue
            o = order(r, m)
            if o is not None and o == k:  # faithful
                found = (r, o); break
        if found:
            N = m * k
            out.append((N, m, k, found[0], found[1], N * math.exp(-w / N)))
out.sort()
for N, m, k, r, o, mu in out[:200]:
    print(m, k, r, o, N, f"{mu:.2f}")
