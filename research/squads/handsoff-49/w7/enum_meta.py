"""List metacyclic groups Z_m x|_r Z_k with N = m k in [lo, hi], k even (so an involution (0,k/2) exists).
r runs over one representative per cyclic subgroup of (Z/m)^* with r^k = 1 (r != 1)."""
import sys
from math import gcd
lo, hi = int(sys.argv[1]), int(sys.argv[2])
out = []
for N in range(lo, hi + 1):
    for k in range(2, N + 1, 2):
        if N % k:
            continue
        m = N // k
        if m < 3:
            continue
        seen = set()
        for r in range(2, m):
            if gcd(r, m) != 1 or r in seen:
                continue
            if pow(r, k, m) != 1 % m:
                continue
            # cyclic subgroup <r>
            sub = set()
            x = 1
            for _ in range(m):
                x = x * r % m
                sub.add(x)
                if x == 1:
                    break
            seen |= sub
            out.append((m, k, r, N))
for m, k, r, N in out:
    print(f"meta {m} {k} {r} {N}")
