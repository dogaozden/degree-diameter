# List non-split metacyclic groups <x,y | x^m, y^k = x^s, y x y^-1 = x^r> of order m*k in [5851, 6100].
# Conditions: r^k = 1 (mod m), r*s = s (mod m), s != 0, r != 1 (nonabelian).
from math import gcd
import sys
lo, hi = 5851, 6100
out = []
for N in range(lo, hi + 1):
    for m in range(2, N + 1):
        if N % m:
            continue
        k = N // m
        if k < 2:
            continue
        for r in range(2, m):
            if gcd(r, m) != 1 or pow(r, k, m) != 1 % m:
                continue
            # s with (r-1)*s = 0 mod m, s != 0
            for s in range(1, m):
                if (r * s - s) % m == 0:
                    # keep only the smallest-order representative per (m,k,r) to limit output
                    out.append((N, m, k, r, s))
                    break
# Summaries: number of valid (m,k,r) and per N
print("total (N,m,k,r,s) with some s:", len(out))
sel = []
for N, m, k, r, s in out:
    # order of s in C_m
    o = m // gcd(s, m)
    sel.append((N, m, k, r, s, o))
for row in sel:
    if row[0] in (5852, 5880, 5900, 5940, 6000, 6048, 6080, 6090) or True:
        pass
import collections
byN = collections.Counter(r[0] for r in sel)
print("N values with candidates:", len(byN))
for row in sel[:80]:
    print("N=%d m=%d k=%d r=%d s=%d ord(s)=%d" % row)
