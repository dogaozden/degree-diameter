#!/usr/bin/env python3
# enum2.py Flo Fhi KMIN Nlo Nhi: odd-order metacyclic factors Z_m x|_r Z_k (m odd, any; k odd >= KMIN prime or
# composite; r^k = 1 mod m, ord(r) = k' > 1 with k' | k, gcd(r,m)=1) with N=mk in [Flo,Fhi]; prints pairs
# "N | m k r | m2 k2 r2" with N = N1*N2 in [Nlo, Nhi]. Canonical r: smallest r >= 2 with r^k = 1, ord(r) > 1.
import sys, math
Flo, Fhi, KMIN, Nlo, Nhi = map(int, sys.argv[1:6])
def ordr(r, m):
    x, o = r % m, 1
    while x != 1 % m:
        x = x * r % m; o += 1
    return o
F = []
for k in range(KMIN, Fhi, 2):
    if k % 2 == 0: continue
    for m in range(1, Fhi // k + 1, 2):
        N = m * k
        if N < Flo or N > Fhi or m < 3: continue
        # the smallest r >= 2 with r^k = 1 mod m and r of order > 1 (needs gcd(r,m)=1)
        best = None
        for r in range(2, m):
            if math.gcd(r, m) != 1: continue
            if pow(r, k, m) != 1 % m: continue
            if pow(r, 1, m) == 1: continue
            best = r; break
        if best is not None: F.append((N, m, k, best))
F.sort()
out = []
for a in F:
    for b in F:
        if a[0] > b[0]: continue
        N = a[0] * b[0]
        if Nlo <= N <= Nhi: out.append((N, a, b))
out.sort()
for N, a, b in out:
    print(f"{N} | {a[1]} {a[2]} {a[3]} | {b[1]} {b[2]} {b[3]}")
