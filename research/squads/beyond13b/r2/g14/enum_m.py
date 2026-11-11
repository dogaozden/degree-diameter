#!/usr/bin/env python3
"""enum_m.py lo hi [kmax]: every m that is a product of prime powers p^e with p = 1 mod k (k odd prime, 13..kmax),
m >= 2 prime factors or a prime power, N = m k in [lo, hi]. Trivial centre needs gcd(r-1, m) = 1 and ord(r) = k, which
holds for each prime p | m when p = 1 mod k. Prints "k m N nprimefactors".
"""
import sys
from math import isqrt
sys.path.insert(0, '/home/user/degree-diameter/g14_dummy') if False else None
def isp(x):
    if x < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if x % p == 0: return x == p
    dd, s = x - 1, 0
    while dd % 2 == 0: dd //= 2; s += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        y = pow(a, dd, x)
        if y in (1, x-1): continue
        for _ in range(s-1):
            y = y*y % x
            if y == x-1: break
        else: return False
    return True
lo, hi = int(sys.argv[1]), int(sys.argv[2]); kmax = int(sys.argv[3]) if len(sys.argv) > 3 else 61
res = []
for k in [x for x in range(13, kmax+1, 2) if isp(x)]:
    mlo, mhi = lo // k, hi // k
    P = [p for p in range(k+1, mhi+1, k) if p % 2 == 1 and isp(p)]
    # all products of prime powers from P, with product in [mlo, mhi]
    def rec(idx, cur, nf):
        if lo <= cur * k <= hi and nf >= 1: res.append((k, cur, cur * k, nf))
        for i in range(idx, len(P)):
            p = P[i]
            if cur * p > mhi: break
            pw = p
            while cur * pw <= mhi:
                rec(i + 1, cur * pw, nf + 1)
                pw *= p
    rec(0, 1, 0)
res.sort(key=lambda t: t[2])
for k, m, N, nf in res:
    print(k, m, N, nf)
