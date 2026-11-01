#!/usr/bin/env python3
# pick.py d D Nlo Nhi kmin kmax : groups Z_m x|_r Z_k (any m, r^k=1 mod m, r of exact order k), Nlo<=m*k<=Nhi
import sys, math
from math import gcd
def W(d, D):
    return sum(d * (d - 1) ** (2 * i) for i in range(D // 2)) if D % 2 == 0 else 1 + sum(d*(d-1)**(2*i-1) for i in range(1,(D-1)//2+1))
d, D, lo, hi, kmin, kmax = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6])
w = W(d, D)
out = []
for k in range(kmin, kmax + 1):
    for m in range(max(3, lo // k), hi // k + 2):
        if m * k < lo or m * k > hi: continue
        if m % k == 0 and False: continue
        # find r with exact order k mod m
        r_found = None
        for r in range(2, m):
            if gcd(r, m) != 1: continue
            if pow(r, k, m) != 1: continue
            if all(pow(r, k // p, m) != 1 for p in range(2, k + 1) if k % p == 0 and all(p % q for q in range(2, p))):
                r_found = r; break
        if r_found is None: continue
        N = m * k
        out.append((N, m, k, r_found, N * math.exp(-w / N)))
out.sort()
for N, m, k, r, mu in out[:60]:
    print(m, k, r, N, f"{mu:.2f}")
