#!/usr/bin/env python3
# enum.py Nlo Nhi kmin kmax [per=2]: metacyclic groups Z_m x|_r Z_k, N = m k in [Nlo,Nhi], r of exact order k mod m (or largest
# order dividing k, > 1). Prints "N m k r order".
import sys, math
from math import gcd
Nlo, Nhi, kmin, kmax = map(int, sys.argv[1:5]); per = int(sys.argv[5]) if len(sys.argv) > 5 else 2
def order(r, m):
    x, o = r % m, 1
    while x != 1 % m:
        x = x * r % m; o += 1
        if o > 10**6: return None
    return o
out = []
for N in range(Nlo, Nhi + 1):
    for k in range(kmin, kmax + 1):
        if N % k: continue
        m = N // k
        if m < 3: continue
        if k >= m: continue
        best = []
        # search units r with r^k = 1 and order > 1
        for r in range(2, m):
            if gcd(r, m) != 1: continue
            if pow(r, k, m) != 1 % m: continue
            o = order(r, m)
            if o is None or o == 1: continue
            best.append((o, r))
            if len(best) >= 40: break
        best.sort(key=lambda t: (-t[0], t[1]))
        seen = 0
        for o, r in best:
            if seen >= per: break
            out.append((N, m, k, r, o)); seen += 1
for N, m, k, r, o in out:
    print(N, m, k, r, o)
