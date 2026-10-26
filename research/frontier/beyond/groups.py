#!/usr/bin/env python3
"""List SL(2,p) x Z_n and PSL(2,p) x Z_n groups whose mu = N exp(-W/N) lies in [lo, hi] for a cell (d, D).
n = 1 or n with every prime factor = 1 mod 3 (the order-3 automorphism z -> r z then fixes only 0), gcd(p, n) = 1.
usage: groups.py d D mu_lo mu_hi [max_lines] [nmax]"""
import math, sys
sys.path.insert(0, __import__('os').path.dirname(__file__))
from plan import W

def isprime(x):
    if x < 2: return False
    for r in range(2, int(x ** 0.5) + 1):
        if x % r == 0: return False
    return True

def good_n(n):
    if n == 1: return True
    m = n
    for r in range(2, int(n ** 0.5) + 2):
        while m % r == 0:
            if r % 3 != 1: return False
            m //= r
    return m == 1 or m % 3 == 1

def mu(d, D, N): return N * math.exp(-W(d, D) / N)

if __name__ == "__main__":
    d, D, lo, hi = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3]), float(sys.argv[4])
    mx = int(sys.argv[5]) if len(sys.argv) > 5 else 40
    nmax = int(sys.argv[6]) if len(sys.argv) > 6 else 2000   # keep the abelian part small (quotient bound)
    out = []
    for p in range(5, 2000):
        if not isprime(p): continue
        for fam, base in (("sl", p * (p * p - 1)), ("psl", p * (p * p - 1) // 2)):
            # n range from mu window
            for n in range(1, nmax + 1):
                N = base * n
                m = mu(d, D, N)
                if m > hi: break
                if m < lo or math.gcd(p, n) != 1 or not good_n(n): continue
                out.append((N, fam, p, n, m))
    out.sort()
    for N, fam, p, n, m in out[:mx] if len(out) <= mx else [out[i * len(out) // mx] for i in range(mx)]:
        print(f"{fam} {p} {n}  N={N:,}  2N={2*N:,}  mu={m:.2f}")
