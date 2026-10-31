# m = 2p (p prime), s = p (order 2 in C_m), r odd with r mod p of order d > 1, d | k; N = 2 p k in [5851, 6100].
from math import gcd
def isprime(n):
    return n > 1 and all(n % q for q in range(2, int(n**0.5) + 1))
out = []
for p in range(2, 3100):
    if not isprime(p): continue
    for k in range(4, 80):
        N = 2 * p * k
        if not (5851 <= N <= 6100): continue
        m = 2 * p
        rs = []
        for r in range(3, m, 2):          # r odd
            if r % p == 1 % p: continue   # r = 1 mod p gives abelian
            if pow(r, k, m) != 1: continue
            d = next(t for t in range(1, k + 1) if pow(r, t, m) == 1) if False else None
            rs.append(r)
        if rs:
            out.append((N, p, m, k, rs))
for N, p, m, k, rs in out:
    # order of r mod p
    def ordmod(r):
        t, x = 1, r % p
        while x != 1 % p:
            x = x * r % p; t += 1
        return t
    ords = sorted(set(ordmod(r) for r in rs))
    print("N=%d p=%d m=%d k=%d  #r=%d  orders of r mod p: %s  e.g. r=%s" % (N, p, m, k, len(rs), ords, rs[:6]))
