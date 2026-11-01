#!/usr/bin/env python3
"""Candidate groups SL(2,p) x Z_n and PSL(2,p) x Z_n for an orbit search with automorphism order k (odd prime):
p prime with k | (p-1)(p+1) (an element of order k in PSL(2,p)), n = 1 or every prime factor of n = 1 mod k
(z -> r z of order k fixes only 0), gcd(p, n) = 1.  mu = N exp(-W/N) with W as in ../beyond/plan.py.
usage: grp.py d D mu_lo mu_hi [k=3] [max_lines=40] [nmax=3000] [pmin=5] [pmax=2000]"""
import math, sys
sys.path.insert(0, __import__('os').path.join(__import__('os').path.dirname(__file__), '../beyond'))
from plan import W
def isprime(x):
    if x < 2: return False
    i = 2
    while i * i <= x:
        if x % i == 0: return False
        i += 1
    return True
def good_n(n, k):
    m, r = n, 2
    while r * r <= m:
        while m % r == 0:
            if r % k != 1: return False
            m //= r
        r += 1
    return m == 1 or m % k == 1
a = sys.argv
d, D, lo, hi = int(a[1]), int(a[2]), float(a[3]), float(a[4])
k = int(a[5]) if len(a) > 5 else 3
mx = int(a[6]) if len(a) > 6 else 40
nmax = int(a[7]) if len(a) > 7 else 3000
pmin = int(a[8]) if len(a) > 8 else 5
pmax = int(a[9]) if len(a) > 9 else 2000
w = W(d, D); out = []
for p in range(pmin, pmax + 1):
    if not isprime(p) or p == k or ((p - 1) * (p + 1)) % k: continue
    for fam, base in (("sl", p * (p * p - 1)), ("psl", p * (p * p - 1) // 2)):
        for n in range(1, nmax + 1):
            N = base * n; m = N * math.exp(-w / N)
            if m > hi: break
            if m < lo or math.gcd(p, n) != 1 or not (n == 1 or good_n(n, k)): continue
            out.append((N, fam, p, n, m))
out.sort()
sel = out if len(out) <= mx else [out[i * len(out) // mx] for i in range(mx)]
for N, fam, p, n, m in sel:
    print(f"{fam} {p} {n}  N={N:,}  vertices={2*N:,}  mu={m:.2f}")
