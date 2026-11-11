#!/usr/bin/env python3
# enumerate odd metacyclic Z_m x|_r Z_k with k in [13,61], N=m*k in [lo,hi]; one line per subgroup "N m k r d fpf"
import sys
from math import gcd
lo, hi = int(sys.argv[1]), int(sys.argv[2])
out = []
for k in range(13, 62, 2):
    for N in range((lo + k - 1) // k * k, hi + 1, k):
        if N % 2 == 0: continue
        m = N // k
        if m < 3: continue
        seen = set()
        for r in range(2, m):
            if gcd(r, m) != 1 or pow(r, k, m) != 1 % m: continue
            # exact order d of r, d | k
            d = 1; x = r % m
            while x != 1 % m:
                x = x * r % m; d += 1
            if d < 13: continue
            sub = frozenset(pow(r, j, m) for j in range(d))
            if sub in seen: continue
            seen.add(sub)
            fpf = int(all(gcd(pow(r, j, m) - 1, m) == 1 for j in range(1, d)))
            out.append((N, m, k, r, d, fpf))
for row in sorted(out, key=lambda t: (-t[5], t[0])):
    print(*row)
