#!/usr/bin/env python3
"""pick.py d D mu_lo mu_hi [k] [maxn]: groups SL(2,p) x Z_n and PSL(2,p) x Z_n (p prime >= 5, n = 1 or n a prime = 1 mod k, and k | p-1 or p+1, gcd(p,n) = 1) whose size-law mu = N exp(-W/N) lies in [mu_lo, mu_hi].  Sorted by N.
Size law: research/frontier/SIZE_LAW.md; W as in research/frontier/beyond/plan.py (odd D: per-side same-side words)."""
import math, sys
def W(d, D):
    if D % 2 == 0: return sum(d * (d - 1) ** (2 * i) for i in range(D // 2))
    return 1 + sum(d * (d - 1) ** (2 * i - 1) for i in range(1, (D - 1) // 2 + 1))
def isprime(x):
    if x < 2: return False
    i = 2
    while i * i <= x:
        if x % i == 0: return False
        i += 1
    return True
def has_order_k(n, k):
    if n == 1: return True
    return any(math.gcd(r, n) == 1 and pow(r, k, n) == 1 for r in range(2, n))
d, D, lo, hi = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3]), float(sys.argv[4])
k = int(sys.argv[5]) if len(sys.argv) > 5 else 3
maxn = int(sys.argv[6]) if len(sys.argv) > 6 else 2000
w = W(d, D); out = []
for p in range(5, 3000):
    if not isprime(p): continue
    if k > 2 and (p - 1) % k and (p + 1) % k and p != k: continue   # an element of projective order k in SL(2,p)
    for fam, base in (("sl", p * (p * p - 1)), ("psl", p * (p * p - 1) // 2)):
        if base > 2e10: continue
        for n in range(1, maxn + 1):
            N = base * n
            if N > 2.2e10: break
            if math.gcd(p, n) != 1: continue
            mu = N * math.exp(-w / N)
            if mu < lo or mu > hi: continue
            if n > 1 and not (isprime(n) and n % k == 1): continue
            out.append((N, fam, p, n, mu))
out.sort()
for N, fam, p, n, mu in out: print(f"{fam} {p} {n} N={N} 2N={2*N} mu={mu:.2f}")
