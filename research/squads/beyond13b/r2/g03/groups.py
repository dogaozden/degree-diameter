#!/usr/bin/env python3
# groups.py: for odd composite k, primes m = 1 mod 2k with N = m k in [lo, hi], r = g^((m-1)/k) mod m of exact order k.
# Prints "m k r N mu" with mu = N exp(-W/N), W = 22369621 (d=5, D=13).
import sys, math
LO, HI = 1854000, 1950000
W = 22369621
def isprime(x):
    if x < 2: return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if x % p == 0: return x == p
    dd, s = x - 1, 0
    while dd % 2 == 0: dd //= 2; s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        y = pow(a, dd, x)
        if y in (1, x - 1): continue
        for _ in range(s - 1):
            y = y * y % x
            if y == x - 1: break
        else: return False
    return True
def primes_of(n):
    ps, q = [], 2
    while q * q <= n:
        if n % q == 0:
            ps.append(q)
            while n % q == 0: n //= q
        q += 1
    if n > 1: ps.append(n)
    return ps
ks = [int(x) for x in sys.argv[1].split(',')] if len(sys.argv) > 1 else [39, 45, 51, 57, 63, 33]
for k in ks:
    ps = primes_of(k)
    out = []
    m = LO // k + 1
    while m * k <= HI:
        if m % 2 == 1 and (m - 1) % (2 * k) == 0 and m * k >= LO and isprime(m):
            g = 2
            while True:
                r = pow(g, (m - 1) // k, m)
                if pow(r, k, m) == 1 and all(pow(r, k // q, m) != 1 for q in ps):
                    break
                g += 1
            N = m * k
            out.append((N, m, r, g))
        m += 1
    out.sort()
    for N, m, r, g in out:
        print(m, k, r, N, f"{N * math.exp(-W / N):.3f}", f"g={g}")
