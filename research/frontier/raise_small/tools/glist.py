#!/usr/bin/env python3
"""glist.py Nlo Nhi [kmin] [dmin] [--odd] [--fpf]: non-abelian metacyclic groups Z_m x|_r Z_k, Nlo <= m k <= Nhi.

One line "N m k r d fpf" per (m, k, <r>): r runs over generators of the cyclic subgroups of Z_m^* whose order d divides k
and is >= dmin (default 2; d < k means a non-faithful action, i.e. a central Z_(k/d) inside Z_k). Different r with the
same <r> give isomorphic groups, so one r per subgroup. fpf = 1 if r^j - 1 is a unit mod m for 0 < j < d (Frobenius
kernel; with d = k the group is a Frobenius group). Not a classification: isomorphic groups can appear more than once.
"""
import sys
from math import gcd


def mult_order(r, m):
    x, d = r % m, 1
    while x != 1 % m:
        x = x * r % m; d += 1
        if d > m: return 0
    return d


def main():
    a = [x for x in sys.argv[1:] if not x.startswith('--')]
    lo, hi = int(a[0]), int(a[1]); kmin = int(a[2]) if len(a) > 2 else 2; dmin = int(a[3]) if len(a) > 3 else 2
    odd = '--odd' in sys.argv; fpfonly = '--fpf' in sys.argv
    for N in range(lo, hi + 1):
        if odd and N % 2 == 0: continue
        for k in range(kmin, N // 3 + 1):
            if N % k: continue
            m = N // k
            if m < 3: continue
            seen = set()
            for r in range(2, m):
                if gcd(r, m) != 1: continue
                d = mult_order(r, m)
                if d < dmin or k % d: continue
                sub = frozenset(pow(r, j, m) for j in range(d))
                if sub in seen: continue
                seen.add(sub)
                fpf = int(all(gcd(pow(r, j, m) - 1, m) == 1 for j in range(1, d)))
                if fpfonly and not fpf: continue
                print(N, m, k, r, d, fpf)


if __name__ == '__main__':
    main()
