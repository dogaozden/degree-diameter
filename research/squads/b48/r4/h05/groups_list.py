import math
from math import gcd
out = []
for N in range(101, 131):
    cands = []
    for k in range(2, N + 1):
        if N % k: continue
        m = N // k
        if m < 2: continue
        for r in range(2, m):
            if gcd(r, m) != 1: continue
            # order of r mod m must divide k, r != 1
            x, o = r, 1
            while x != 1 and o <= k:
                x = x * r % m; o += 1
            if x != 1 or o > k or o == 1: continue
            if o != k and k % o: continue
            if o < 2: continue
            cands.append((m, k, r, o))
    # keep: prefer r of order exactly k (or largest), at most 2 per N, dedupe by (m,k)
    seen = set(); pick = []
    for (m, k, r, o) in sorted(cands, key=lambda t: (-t[3], t[0])):
        if (m, k) in seen: continue
        seen.add((m, k)); pick.append((m, k, r, o))
    for p in pick[:2]:
        out.append((N, p))
for N, (m, k, r, o) in out:
    print(N, f"meta:{m}:{k}:{r}", "ord_r=", o)
