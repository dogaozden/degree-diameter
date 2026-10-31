#!/usr/bin/env python3
"""all_list.py LO HI: formula-only groups of order N in [LO, HI] for fsd, one per line "N kind args" (fsd arguments):
  meta m k r 1        C_m : C_k (meta_list.py rules: one r per subgroup <r>, d = ord(r) >= 3, every prime of m moved)
  meta m k r n3       (C_m : C_k) x C_n3, n3 >= 2, base as above
  aff p f k n3        F_q : C_k x C_n3, q = p^f, f >= 2, k | q - 1, k does not divide p^g - 1 for any proper g | f
                      (otherwise omega^((q-1)/k) lies in a subfield and x, y do not generate)
  psl p n3, sl p n3   p prime >= 5
Sorted by N, then kind."""
import sys
from math import gcd
sys.path.insert(0, __file__.rsplit("/", 1)[0])


def isprime(n):
    return n > 1 and all(n % d for d in range(2, int(n ** 0.5) + 1))


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


def metas(N, mind=3, minm=7):
    out = []
    for m in range(minm, N // 2 + 1):
        if N % m:
            continue
        k = N // m
        ps = primes_of(m)
        seen = set()
        for r in range(2, m):
            if gcd(r, m) != 1 or pow(r, k, m) != 1 or any((r - 1) % p == 0 for p in ps):
                continue
            d = order(r, m)
            if d < mind:
                continue
            sub = frozenset(pow(r, e, m) for e in range(d))
            if sub in seen:
                continue
            seen.add(sub)
            out.append((m, k, r, d))
    return out


def main():
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    rows = []
    for N in range(lo, hi + 1):
        for n3 in range(1, 13):
            if N % n3:
                continue
            for m, k, r, d in metas(N // n3):
                rows.append((N, 0, f"meta {m} {k} {r} {n3}"))
            for p in range(2, 200):
                if not isprime(p):
                    continue
                for f in range(2, 8):
                    q = p ** f
                    if q > N // n3:
                        break
                    if (N // n3) % q:
                        continue
                    k = N // n3 // q
                    if (q - 1) % k:
                        continue
                    if any(f % g == 0 and (p ** g - 1) % k == 0 for g in range(1, f)):
                        continue
                    rows.append((N, 1, f"aff {p} {f} {k} {n3}"))
            for p in range(5, 200):
                if not isprime(p):
                    continue
                o = p * (p * p - 1) // 2
                if o * n3 == N:
                    rows.append((N, 2, f"psl {p} {n3}"))
                if 2 * o * n3 == N:
                    rows.append((N, 2, f"sl {p} {n3}"))
    rows.sort()
    for N, _, s in rows:
        print(N, s)


if __name__ == "__main__":
    main()
