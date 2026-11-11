#!/usr/bin/env python3
# pick2.py Nlo Nhi kmin : for each odd m, k >= kmin with m k in [Nlo, Nhi], list one r per distinct cyclic subgroup
# <r> of order exactly k in (Z/m)^* (distinct subgroups give non-isomorphic Z_m x|_r Z_k in general). "N m k r"
import sys
from math import gcd
lo, hi, kmin = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
rows = []
for k in range(kmin, hi // 3 + 1):
    for m in range(max(3, -(-lo // k)) | 1, hi // k + 1, 2):
        N = m * k
        if N < lo or N > hi: continue
        seen = set(); reps = []
        for r in range(2, m):
            if gcd(r, m) != 1 or pow(r, k, m) != 1: continue
            sub = []; x = 1
            for _ in range(k): sub.append(x); x = x * r % m
            if x != 1 % m: continue
            # order of r must be exactly k
            if len(set(sub)) != k: continue
            fs = frozenset(sub)
            if fs in seen: continue
            seen.add(fs); reps.append(r)
        for r in reps: rows.append((N, m, k, r))
rows.sort()
for row in rows: print(*row)
