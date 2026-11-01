#!/usr/bin/env python3
"""cands.py d D lo hi [sl|psl|both] [pmax]: SL(2,p) x Z_n / PSL(2,p) x Z_n with lo <= 2N <= hi (vertices),
n = 1 or n with an element of order 3 mod n (needed by haar_big0's alpha), gcd(p, n) = 1.
Prints: fam p n 2N mu lam special, where mu = N exp(-W/N) (size law, per side), lam = W/N, and special = expected
odd-D special holes (ODD_D_HOLES.md): central elements (2n for SL, n for PSL) * exp(-lam/h), h = (D-1)/2, plus PSL
involutions (~p^2/2) * exp(-lam/2). Sorted by 2N descending."""
import sys, math
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
def phi(n):
    r, m, q = n, n, 2
    while q * q <= m:
        if m % q == 0:
            while m % q == 0: m //= q
            r -= r // q
        q += 1
    if m > 1: r -= r // m
    return r
def has_ord3(n):
    return n == 1 or phi(n) % 3 == 0   # (Z/n)* has an element of order 3 iff 3 | phi(n)
d, D, lo, hi = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3]), float(sys.argv[4])
fams = sys.argv[5] if len(sys.argv) > 5 else 'both'
pmax = int(sys.argv[6]) if len(sys.argv) > 6 else 3000
NMAX = int(sys.argv[7]) if len(sys.argv) > 7 else 400
w = W(d, D); h = (D - 1) // 2
out = []
for p in range(5, pmax + 1):
    if not isprime(p): continue
    for fam in ('sl', 'psl'):
        if fams != 'both' and fam != fams: continue
        g = p * (p * p - 1) // (2 if fam == 'psl' else 1)
        nlo, nhi = max(1, math.ceil(lo / 2 / g)), min(int(hi / 2 / g), NMAX)
        for n in range(nlo, nhi + 1):
            if math.gcd(n, p) != 1 or not has_ord3(n): continue
            N = g * n; lam = w / N; D2 = D % 2
            spec = 0.0
            if D2:
                spec = (2 * n if fam == 'sl' else n) * math.exp(-lam / h)
                if fam == 'psl': spec += p * p / 2 * math.exp(-lam / 2)
            out.append((2 * N, fam, p, n, N * math.exp(-lam), lam, spec))
out.sort(reverse=True)
for v in out: print(f"{v[1]} {v[2]} {v[3]} {v[0]:.6g} mu={v[4]:.2f} lam={v[5]:.2f} special={v[6]:.2f}")
