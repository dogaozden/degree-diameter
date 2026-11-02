#!/usr/bin/env python3
# enum.py: candidate metacyclic groups Z_m x|_r Z_k (k odd composite, m prime or m = p*q) with N = m*k (or p*q*k)
# just above the record N0 = 1797455; prints "kind m k r N mu" sorted by N (smallest first).
import sys, math
W = 22369621  # W(5,13) for D odd: 1 + sum_{i=1..6} 5*4^(2i-1)
d=5
def isp(x):
    if x < 2: return False
    i = 2
    while i*i <= x:
        if x % i == 0: return False
        i += 1
    return True
def order(r, m):
    x, o = r % m, 1
    while x != 1 % m:
        x = x * r % m; o += 1
        if o > 10**6: return None
    return o
def divisors(n): return [x for x in range(1, n+1) if n % x == 0]
def elem_of_order(m, k):
    # an r mod m with exact multiplicative order k (m prime, k | m-1)
    from itertools import count
    for g in range(2, m):
        if math.gcd(g, m) != 1: continue
        r = pow(g, (m - 1) // k, m)
        if order(r, m) == k: return r
    return None
N0 = 1797455
res = []
ks = [int(x) for x in sys.argv[1].split(',')] if len(sys.argv) > 1 else [15,21,25,27,33,35,39,45,51,55,57,63]
hi = float(sys.argv[2]) if len(sys.argv) > 2 else 1.95e6
for k in ks:
    # kind A: m prime, m = 1 mod k
    m = k + 1
    while m * k <= hi:
        if m * k > N0 and isp(m) and m % k == 1 % k:
            r = elem_of_order(m, k)
            if r is not None:
                N = m * k
                res.append((N, 'prime', m, k, r))
        m += k
    # kind B: m = p*q, p,q primes = 1 mod k (distinct), r of exact order k mod p and mod q
    ps = [p for p in range(k+1, int(hi/(k*k))+2, k) if isp(p)]
    for i, p in enumerate(ps):
        for q in ps[i:]:
            if q == p: continue
            m = p*q; N = m*k
            if N > N0 and N <= hi:
                rp = elem_of_order(p, k); rq = elem_of_order(q, k)
                if rp is None or rq is None: continue
                # CRT: r = rp mod p, rq mod q
                r = None
                for t in range(1, m):
                    pass
                r = (rp * q * pow(q, -1, p) + rq * p * pow(p, -1, q)) % m
                assert order(r, m) == k
                res.append((N, 'pq', m, k, r))
res.sort()
for N, kind, m, k, r in res:
    mu = N*math.exp(-W/N)
    print(kind, m, k, r, N, f"{mu:.3f}")
