#!/usr/bin/env python3
"""pick11.py d [lo_frac hi_frac]: candidate groups for (d,11) with N in (N_rec*lo, N_rec*hi]:
SL(2,p) x Z_n and PSL(2,p) x Z_n (n = 1 or n with an r of order 3 mod n, gcd(p,n)=1, 3 | p-1 or p+1 or p=3),
and Frobenius Z_q x| Z_k (q prime, k | q-1, k odd 13..99).  Prints N, 2N, mu (size law, per side), gain %."""
import math, sys
REC = {3:1474,4:30334,5:311426,6:2122518,7:11012976,8:45329808,9:155250816,10:460691568,11:1241299248,
       12:2976066240,13:6781213392,14:14381398080,15:28655908512,16:29961590400}
def W(d, D=11): return 1 + sum(d * (d - 1) ** (2 * i - 1) for i in range(1, (D - 1) // 2 + 1))
def isprime(x):
    if x < 2: return False
    i = 2
    while i * i <= x:
        if x % i == 0: return False
        i += 1
    return True
def _pf(m):
    f = 2; r = []
    while f * f <= m:
        while m % f == 0: r.append(f); m //= f
        f += 1
    if m > 1: r.append(m)
    return r
def has3(n):   # n = 1 or a product of distinct primes = 1 mod 3 (then r of order 3 without fixed points other than 0 exists)
    if n == 1: return True
    m = n; f = 2
    while f * f <= m:
        if m % f == 0:
            if f % 3 != 1: return False
            m //= f
            if m % f == 0: return False
        f += 1
    return m == 1 or m % 3 == 1
d = int(sys.argv[1]); lo = float(sys.argv[2]) if len(sys.argv) > 2 else 1.0; hi = float(sys.argv[3]) if len(sys.argv) > 3 else 1.04
fam = sys.argv[4] if len(sys.argv) > 4 else "all"
Nrec = REC[d] // 2; w = W(d); out = []; NMAX = int(sys.argv[5]) if len(sys.argv) > 5 else 400
if fam in ("all", "sl", "psl"):
  for p in range(13, 4000):
    if not isprime(p) or ((p - 1) % 3 and (p + 1) % 3): continue
    for f, base in (("sl", p * (p * p - 1)), ("psl", p * (p * p - 1) // 2)):
        if fam != "all" and f != fam: continue
        if base > Nrec * hi: continue
        nlo = max(1, math.ceil(Nrec * lo / base)); nhi = min(int(Nrec * hi // base), NMAX)
        for n in range(nlo, nhi + 1):
            N = base * n
            if N <= Nrec * lo or N > Nrec * hi or math.gcd(p, n) != 1 or not has3(n): continue
            if n > 1 and n % 2 == 0: continue
            out.append((N, f"{f} {p} {n}"))
if fam == "meta" or (fam == "all" and Nrec < 3e6):
  for k in range(13, 100, 2):
    qlo = int(Nrec * lo / k); qhi = int(Nrec * hi / k) + 1
    for q in range(qlo, qhi + 1):
        if (q - 1) % k or not isprime(q): continue
        N = q * k
        if N <= Nrec * lo or N > Nrec * hi: continue
        g = next(x for x in range(2, q) if all(pow(x, (q - 1) // f, q) != 1 for f in set(_pf(q - 1))))
        out.append((N, f"meta {q} {k} {pow(g, (q - 1) // k, q)}"))
out.sort()
for N, s in out:
    mu = N * math.exp(-w / N)
    print(f"{s:22s} N={N:<14d} 2N={2*N:<14d} mu={mu:8.2f} gain={100*(N/Nrec-1):6.2f}%")
