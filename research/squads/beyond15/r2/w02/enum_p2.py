#!/usr/bin/env python3
# groups Z_2 x (Z_p x|_r Z_k) = metacyclic(p,k,r) x Z_2 (even order, D even): p prime, k | p-1, r of order k mod p
import sys, math
d, D, lo, hi = int(sys.argv[1]), int(sys.argv[2]), int(float(sys.argv[3])), int(float(sys.argv[4]))
def W(d, D):
    return sum(d * (d - 1) ** (2 * i) for i in range(D // 2))
w = W(d, D)
def isp(x):
    if x < 2: return False
    i = 2
    while i * i <= x:
        if x % i == 0: return False
        i += 1
    return True
def primes_of(n):
    ps, p = [], 2
    while p * p <= n:
        if n % p == 0:
            ps.append(p)
            while n % p == 0: n //= p
        p += 1
    if n > 1: ps.append(n)
    return ps
for k in range(int(sys.argv[5]), int(sys.argv[6]) + 1):
    ps = primes_of(k)
    # N = 2 p k
    plo = max(3, lo // (2 * k)); phi = hi // (2 * k)
    p = plo + 1 - (plo % 2) if plo % 2 == 0 else plo
    ps_found = 0
    for p in range(plo, phi + 1):
        if p % k != 1 % k or not isp(p): continue
        # find r of order exactly k mod p
        r = None
        for g in range(2, 500):
            if pow(g, k, p) == 1 and all(pow(g, k // q, p) != 1 for q in ps):
                r = g; break
        if r is None: continue
        N = 2 * p * k
        print(p, k, r, N, f"{N * math.exp(-w / N):.2f}")
