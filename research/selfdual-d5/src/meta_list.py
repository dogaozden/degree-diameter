#!/usr/bin/env python3
"""meta_list.py LO HI [MINM] [MIND]: metacyclic groups C_m : C_k = <x, y | x^m = y^k = 1, y x y^-1 = x^r> of order
n = m k in [LO, HI], one presentation per cyclic subgroup <r> of (Z/m)^* of order d | k (the group depends only on
m, k and <r>), m odd, d >= MIND (default 3), every prime of m moved by y (r != 1 mod p for each p | m, so no central
C_p factor in <x>), m >= MINM (default 7).  Output lines "n m k r d", sorted by n, then by d descending."""
import sys
from math import gcd


def factor(n):
    f, p = [], 2
    while p * p <= n:
        while n % p == 0:
            f.append(p); n //= p
        p += 1
    if n > 1:
        f.append(n)
    return f


def order(r, m):
    if m == 1:
        return 1
    o, x = 1, r % m
    while x != 1:
        x = x * r % m; o += 1
    return o


def main():
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    minm = int(sys.argv[3]) if len(sys.argv) > 3 else 7
    mind = int(sys.argv[4]) if len(sys.argv) > 4 else 3
    rows = []
    for n in range(lo, hi + 1):
        for m in range(minm, n // 2 + 1):
            if n % m or m % 2 == 0:
                continue
            k = n // m
            ps = sorted(set(factor(m)))
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
                rows.append((n, -d, m, k, r))
    rows.sort()
    for n, nd, m, k, r in rows:
        print(n, m, k, r, -nd)


if __name__ == "__main__":
    main()
