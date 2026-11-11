#!/usr/bin/env python3
# enum2.py lo hi kmin: metacyclic Z_m x|_r Z_k with lo <= m*k <= hi, k >= kmin, r of exact order k mod m (one r per (m,k)).
# Prints "N m k r". Faster than tools/enumeta.py: prunes with k | lambda(m) and samples r.
import sys, random
from math import gcd
lo, hi, kmin = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
random.seed(1)
def factor(n):
    f = {}; p = 2
    while p * p <= n:
        while n % p == 0: f[p] = f.get(p, 0) + 1; n //= p
        p += 1
    if n > 1: f[n] = f.get(n, 0) + 1
    return f
def carm(m, fm):
    # lambda(m) from factorization
    L = 1
    for p, e in fm.items():
        if p == 2:
            l = 1 if e == 1 else (2 if e == 2 else 2 ** (e - 2))
        else:
            l = (p - 1) * p ** (e - 1)
        L = L * l // gcd(L, l)
    return L
def ordr(r, m, L, pl):
    o = L
    for p in pl:
        while o % p == 0 and pow(r, o // p, m) == 1: o //= p
    return o
out = []
fcache = {}
for k in range(kmin, hi // 2 + 1):
    mlo = max(2, -(-lo // k)); mhi = hi // k
    for m in range(mlo, mhi + 1):
        if gcd(m, k) == 0: continue
        fm = fcache.get(m)
        if fm is None: fm = factor(m); fcache[m] = fm
        L = carm(m, fm)
        if L % k: continue
        pl = list(factor(L).keys())
        found = None
        for t in range(300):
            r = random.randrange(2, m) if m > 2 else 1
            if gcd(r, m) != 1: continue
            o = ordr(r, m, L, pl)
            if o % k == 0:
                rr = pow(r, o // k, m)
                if ordr(rr, m, L, pl) == k and rr != 1:
                    found = rr; break
        if found is not None:
            out.append((m * k, m, k, found))
out.sort()
for N, m, k, r in out: print(N, m, k, r)
