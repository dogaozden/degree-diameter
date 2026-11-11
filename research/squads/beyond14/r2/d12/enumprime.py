#!/usr/bin/env python3
# enumprime.py Nlo Nhi kmax: metacyclic Z_p x|_r Z_k, p prime, p*k in [Nlo,Nhi], 4 <= k <= kmax, k | p-1,
# r of exact order k mod p (taken from a generator power). Prints "N p k r".
import sys
lo, hi, kmax = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
def isprime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    i = 3
    while i * i <= n:
        if n % i == 0: return False
        i += 2
    return True
def pf(n):
    f, x = set(), n; q = 2
    while q * q <= x:
        while x % q == 0: f.add(q); x //= q
        q += 1
    if x > 1: f.add(x)
    return f
out = []
for k in range(4, kmax + 1):
    qs = pf(k)
    for p in range(lo // k + 1, hi // k + 1):
        if (p - 1) % k or not (lo <= p * k <= hi): continue
        if not isprime(p): continue
        r = None
        for g in range(2, 50):
            h = pow(g, (p - 1) // k, p)
            if pow(h, k, p) == 1 and all(pow(h, k // q, p) != 1 for q in qs):
                r = h; break
        if r is None: continue
        out.append((p * k, p, k, r))
for N, p, k, r in sorted(out): print(N, p, k, r)
