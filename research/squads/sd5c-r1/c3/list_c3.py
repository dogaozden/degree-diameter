#!/usr/bin/env python3
"""list_c3.py LO HI: metacyclic C_m : C_k = <x,y | x^m = y^k = 1, y x y^-1 = x^r> of order N = m k in [LO, HI]
that meta_list.py skips.  One r per cyclic subgroup <r> of (Z/m)^* with r^k = 1 mod m, ord(r) = d >= 2.
  (a) m even, r != 1 mod p for every odd prime p | m (2-part unrestricted).
  (b) m odd, with split prime powers p^e || m (r = 1 mod p^e) whose product U satisfies U > 12.
Output lines "N m k r d cat U", sorted: d >= 6 first, then k descending, then N, m.
"""
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
    rows = []
    for N in range(lo, hi + 1):
        for m in range(3, N // 2 + 1):
            if N % m:
                continue
            k = N // m
            if k < 2:
                continue
            ps = primes_of(m)
            seen = set()
            for r in range(2, m):
                if gcd(r, m) != 1 or pow(r, k, m) != 1:
                    continue
                d = order(r, m)
                if d < 2:
                    continue
                sub = frozenset(pow(r, e, m) for e in range(d))
                if sub in seen:
                    continue
                seen.add(sub)
                if m % 2 == 0:
                    if any(p != 2 and (r - 1) % p == 0 for p in ps):
                        continue  # some odd prime not moved: already in meta_list / direct-product family
                    cat, U = "a", 0
                else:
                    split = []
                    for p in ps:
                        pe = 1
                        mm = m
                        while mm % p == 0:
                            mm //= p
                            pe *= p
                        if (r - 1) % pe == 0:
                            split.append(pe)
                    if not split:
                        continue  # fully moved: meta_list.py territory
                    U = 1
                    for q in split:
                        U *= q
                    if U <= 12:
                        continue
                    cat = "b"
                rows.append((-(d >= 6), -k, N, -m, r, d, cat, U))
    rows.sort()
    for nd6, nk, N, nm, r, d, cat, U in rows:
        print(N, -nm, -nk, r, d, cat, U)


if __name__ == "__main__":
    main()
