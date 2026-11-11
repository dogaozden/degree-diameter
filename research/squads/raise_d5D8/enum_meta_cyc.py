#!/usr/bin/env python3
"""Metacyclic x cyclic groups (Z_m x|_r Z_k) x Z_n of order N = m*k*n with n >= 2, in a window.

Reuses enum_meta.canon for the isomorphism-light reduction of (m, k, r). Output: "N m k r n" per line.
Usage: enum_meta_cyc.py LO HI
"""
import sys
from math import gcd
from enum_meta import canon

def main():
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    for N in range(lo, hi + 1):
        for n in range(2, N + 1):
            if N % n:
                continue
            sub = N // n
            for k in range(2, sub + 1):
                if sub % k:
                    continue
                m = sub // k
                if m < 2:
                    continue
                seen = set()
                for r in range(1, m):
                    if gcd(r, m) != 1 or pow(r, k, m) != 1 % m:
                        continue
                    c = canon(m, k, r)
                    if c in seen:
                        continue
                    seen.add(c)
                    print(N, m, k, c, n)

if __name__ == "__main__":
    main()
