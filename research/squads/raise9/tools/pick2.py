#!/usr/bin/env python3
"""pick2.py d D mu_lo mu_hi [maxn] [nmode]: SL(2,q) x Z_n and PSL(2,q) x Z_n (q = p^e a prime power >= 4, ANY n >= 1 with
gcd(p, n) = 1) whose size-law mu = N exp(-W/N) is in [mu_lo, mu_hi], sorted by N.  nmode: 'any' (default) or 'r3'
(n = 1 or n has an element r of order 3 mod n, needed for alpha to move Z_n in haar_big0 / haar_sym ORBIT).
Also prints the number of r of order 3 mod n.  haar_big0 needs q prime; haar_sym / haar_gen3 take prime powers.
(job raise-d9, 2026-11-01; W as in research/frontier/beyond11/pick.py)"""
import math, sys
def W(d, D):
    if D % 2 == 0: return sum(d * (d - 1) ** (2 * i) for i in range(D // 2))
    return 1 + sum(d * (d - 1) ** (2 * i - 1) for i in range(1, (D - 1) // 2 + 1))
def ppow(q):
    for p in range(2, q + 1):
        if q % p == 0:
            e = 0; x = q
            while x % p == 0: x //= p; e += 1
            return (p, e) if x == 1 else None
d, D, lo, hi = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3]), float(sys.argv[4])
maxn = int(sys.argv[5]) if len(sys.argv) > 5 else 400
mode = sys.argv[6] if len(sys.argv) > 6 else 'any'
w = W(d, D); out = []
for q in range(4, 3000):
    pe = ppow(q)
    if not pe: continue
    p, e = pe
    for fam, base in (("sl", q * (q * q - 1)), ("psl", q * (q * q - 1) // (2 if p > 2 else 1))):
        if fam == "psl" and p == 2: continue
        for n in range(1, maxn + 1):
            N = base * n
            if N > 3e10: break
            if math.gcd(p, n) != 1: continue
            mu = N * math.exp(-w / N)
            if mu < lo or mu > hi: continue
            r3 = sum(1 for r in range(2, n) if math.gcd(r, n) == 1 and pow(r, 3, n) == 1) if n > 1 else 0
            if mode == 'r3' and n > 1 and r3 == 0: continue
            out.append((N, fam, q, e, n, mu, r3))
out.sort()
for N, fam, q, e, n, mu, r3 in out:
    print(f"{fam} {q}{'' if e == 1 else ' (p^%d)' % e} n={n} N={N} 2N={2*N} mu={mu:.2f} r3={r3}")
