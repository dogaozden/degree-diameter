#!/usr/bin/env python3
# enum.py k lo hi : SL/PSL(2,p) x Z_n with 2N in [lo,hi], p ≡ ±1 (mod k) (k-element in PSL/SL(2,p)), n with
# an element r of order k mod n or n with no such element (then r = 1), gcd(p,n)=1. prints fam p n 2N mu
import sys, math
def isprime(x):
    if x < 2: return False
    i = 2
    while i * i <= x:
        if x % i == 0: return False
        i += 1
    return True
def W(d, D):
    return 1 + sum(d * (d - 1) ** (2 * i - 1) for i in range(1, (D - 1) // 2 + 1))
k, lo, hi = int(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3])
d, D = 7, 13
w = W(d, D)
res = []
for p in range(5, 2000):
    if not isprime(p): continue
    if (p * p - 1) % k != 0 and not (p % k in (1, k - 1)) and k != 1:
        pass
    ok = (p % k == 1 or p % k == k - 1) if k > 2 else True
    if not ok: continue
    for fam in ('sl', 'psl'):
        g = p * (p * p - 1) // (2 if fam == 'psl' else 1)
        for n in range(1, 400):
            if math.gcd(n, p) != 1: continue
            N = g * n
            if 2 * N < lo or 2 * N > hi: continue
            # order-k element of (Z/n)^* present?
            has = any(pow(r, k, n) == 1 and math.gcd(r, n) == 1 and r != 1 for r in range(2, n)) if n > 1 else False
            lam = w / N
            res.append((2 * N, fam, p, n, N * math.exp(-lam), has))
res.sort()
for r in res: print(f"{r[1]} p={r[2]} n={r[3]} 2N={r[0]} mu={r[4]:.2f} zr={'y' if r[5] else 'n'}")
