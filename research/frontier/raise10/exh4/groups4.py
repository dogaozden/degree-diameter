#!/usr/bin/env python3
"""groups4.py LO HI [all]: metacyclic groups Z_m x|_r Z_k with N = m k in [LO, HI], one r per (m, k, ord(r)) class:
default = Frobenius (m prime, r of order exactly k, k >= 3); 'all' = also composite m and non-faithful r (ord(r) < k,
ord(r) >= 3), one r per multiplicative order (not a full isomorphism classification)."""
import sys, math
lo, hi = int(sys.argv[1]), int(sys.argv[2]); allg = len(sys.argv) > 3
def isprime(x): return x > 1 and all(x % q for q in range(2, int(x ** .5) + 1))
def order(r, m):
    if math.gcd(r, m) != 1: return 0
    o, y = 1, r % m
    while y != 1 % m: y = y * r % m; o += 1
    return o
out = []
for N in range(lo, hi + 1):
    for k in range(3, N // 5 + 1):
        if N % k: continue
        m = N // k
        if m < 5: continue
        if not allg and not isprime(m): continue
        seen = set()
        for r in range(2, m):
            o = order(r, m)
            if o < 3 or k % o or o in seen: continue
            if not allg and o != k: continue
            seen.add(o); out.append((N, m, k, r, o))
            if not allg: break
for t in out: print(*t)
