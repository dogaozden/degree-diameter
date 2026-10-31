#!/usr/bin/env python3
"""meta_list.py LO HI [MIND] [MINM]: metacyclic groups C_m : C_k = <x, y | x^m = y^k = 1, y x y^-1 = x^r> of order
N = m k in [LO, HI], one presentation per cyclic subgroup <r> of (Z/m)^* whose order d divides k (the group depends
only on m, k and <r>), d >= MIND (default 3), m >= MINM (default 7), every prime of m moved by y (r != 1 mod p for
each p | m; otherwise C_p splits off and the group is a direct product, run those as "meta m' k r' n3").
Output lines "N m k r d", sorted by N, then d descending, then m descending."""
import sys
from math import gcd


def primes_of(n):
    ps, p = [], 2
    while p * p <= n:
        if n % p == 0:
            ps.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        ps.append(n)
    return ps


def order(r, m):
    o, x = 1, r % m
    while x != 1 % m:
        x = x * r % m
        o += 1
    return o


def main():
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    mind = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    minm = int(sys.argv[4]) if len(sys.argv) > 4 else 7
    rows = []
    for N in range(lo, hi + 1):
        for m in range(minm, N // 2 + 1):
            if N % m:
                continue
            k = N // m
            ps = primes_of(m)
            seen = set()
            for r in range(2, m):
                if gcd(r, m) != 1 or pow(r, k, m) != 1:
                    continue
                if any((r - 1) % p == 0 for p in ps):
                    continue
                d = order(r, m)
                if d < mind:
                    continue
                sub = frozenset(pow(r, e, m) for e in range(d))
                if sub in seen:
                    continue
                seen.add(sub)
                rows.append((N, -d, -m, k, r))
    rows.sort()
    for N, nd, nm, k, r in rows:
        print(N, -nm, k, r, -nd)


if __name__ == "__main__":
    main()
