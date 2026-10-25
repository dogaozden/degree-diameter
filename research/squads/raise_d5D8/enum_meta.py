#!/usr/bin/env python3
"""Enumerate metacyclic groups Z_m x|_r Z_k (r^k = 1 mod m) of order N = m*k in a window.

Isomorphism reduction (cheap, not complete): r is replaced by its least representative
over r -> r^t mod m with gcd(t, k) = 1 (changing the generator of Z_k). Groups with the
same canonical (m, k, r) are the same; different ones may still be isomorphic (e.g. the
same action from a different factorisation), which only costs screening time.
Output: one line per group "N m k r" (r = canonical), sorted by N.
Usage: enum_meta.py LO HI
"""
import sys
from math import gcd

def canon(m, k, r):
    best = r
    pw = [1]
    for _ in range(1, k):
        pw.append(pw[-1] * r % m)
    # powers of r for each unit t mod k: r^t
    for t in range(1, k):
        if gcd(t, k) != 1:
            continue
        rt = 1
        for _ in range(t):
            rt = rt * r % m
        if rt < best:
            best = rt
    return best

def main():
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, N + 1):
            if N % k:
                continue
            m = N // k
            if m < 2:
                continue
            seen = set()
            for r in range(1, m):
                if gcd(r, m) != 1:
                    continue
                if pow(r, k, m) != 1 % m:
                    continue
                c = canon(m, k, r)
                if c in seen:
                    continue
                seen.add(c)
                out.append((N, m, k, c))
    for N, m, k, r in out:
        print(N, m, k, r)

if __name__ == "__main__":
    main()
