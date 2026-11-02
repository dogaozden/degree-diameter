#!/usr/bin/env python3
"""cands_pq.py lo hi [kmax]: metacyclic Z_m x|_r Z_k with COMPOSITE m = p*q (p<q primes, both = 1 mod k, k odd prime),
r of order k mod p and mod q (so r-1 is a unit mod m: trivial centre, odd order). Lists "m k r N mu" for lo <= N = m k <= hi
with one r per isomorphism class of (r_p, r_q) up to powers (we only emit a few random classes per (p,q,k))."""
import sys, math, random
sys.path.insert(0, '/home/user/degree-diameter/research/frontier/beyond13/meta')
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
def W(d, D):
    if D % 2 == 0: return sum(d*(d-1)**(2*i) for i in range(D//2))
    return 1 + sum(d*(d-1)**(2*i-1) for i in range(1, (D-1)//2+1))
d, D = 5, 13
lo, hi = int(sys.argv[1]), int(sys.argv[2]); kmax = int(sys.argv[3]) if len(sys.argv) > 3 else 61
w = W(d, D)
rng = random.Random(7)
out = []
for k in [x for x in range(3, kmax+1, 2) if isp(x)]:
    if k < 13: continue
    # primes p = 1 mod k in range [k+1, hi/(k*2)]: need p*q*k in [lo,hi] with p<q
    ps = [p for p in range(2*k+1, int(math.isqrt(hi // k)) + 2, 2*k) if isp(p)]
    qs = [q for q in range(2*k+1, hi // (k * 2) + 2, 2*k) if isp(q)]
    for p in ps:
        for q in qs:
            if q <= p: continue
            N = p * q * k
            if not (lo <= N <= hi): continue
            m = p * q
            # r_p, r_q of order k: pick random generators of the order-k subgroups; choose r as CRT pair
            def elt_order_k(z):
                while True:
                    g = rng.randrange(2, z - 1)
                    r = pow(g, (z-1)//k, z)
                    if r != 1: return r
            rp = elt_order_k(p); rq = elt_order_k(q)
            # CRT
            r = (rp * q * pow(q, -1, p) + rq * p * pow(p, -1, q)) % m
            assert pow(r, k, m) == 1 and math.gcd(r, m) == 1 and (r - 1) % p and (r - 1) % q
            out.append((N, m, k, r, p, q, N * math.exp(-w / N)))
out.sort()
for N, m, k, r, p, q, mu in out:
    print(m, k, r, N, f"{mu:.2f}", f"p={p}", f"q={q}")
