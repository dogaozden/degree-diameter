#!/usr/bin/env python3
"""List metacyclic groups C_m : C_k = <x, y | x^m = y^k = 1, y x y^-1 = x^r> with LO <= m k <= HI, one r per cyclic
subgroup <r> of U(m) of order d >= DMIN with d | k (non-abelian when d >= 2), as sdhi factor specs "meta m k r".
Columns: N m k r d inv (number of involutions) -- sorted by inv, then N.
usage: meta_list.py LO HI [DMIN=2] [MAXINV=-1]"""
import sys
from math import gcd


def order(r, m):
    t, d = r % m, 1
    while t != 1 % m:
        t = t * r % m
        d += 1
    return d


def involutions(m, k, r):
    c = 0
    for j in (0, k // 2) if k % 2 == 0 else (0,):
        rj = pow(r, j, m)
        for i in range(m):
            if (i, j) == (0, 0):
                continue
            if (2 * j) % k == 0 and (i + rj * i) % m == 0:
                c += 1
    return c


def main():
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    dmin = int(sys.argv[3]) if len(sys.argv) > 3 else 2
    maxinv = int(sys.argv[4]) if len(sys.argv) > 4 else -1
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            seen = set()
            for r in range(2, m):
                if gcd(r, m) != 1:
                    continue
                d = order(r, m)
                if d < dmin or k % d:
                    continue
                H = frozenset(pow(r, j, m) for j in range(d))
                if H in seen:
                    continue
                seen.add(H)
                inv = involutions(m, k, r)
                if maxinv >= 0 and inv > maxinv:
                    continue
                out.append((inv, N, m, k, r, d))
    out.sort()
    for inv, N, m, k, r, d in out:
        print(N, m, k, r, d, inv)


if __name__ == "__main__":
    main()
