#!/usr/bin/env python3
"""Non-split metacyclic groups G = <a, b | a^m = 1, b^k = a^s, b a b^-1 = a^r> of order N = m k in [LO, HI].

Conditions: r^k = 1 (mod m) and s (r - 1) = 0 (mod m). Only gcd(m, k) > 1 can be non-split (Schur-Zassenhaus);
the split case s = 0 is enum_meta.py. Reduction: s is replaced by d = gcd(s, m) (rescaling a by a unit of m),
r by its least representative over r -> r^u with u a unit mod k (rescaling b; this sends s to s*u, which is
the same class). Partial isomorphism reduction only: different outputs may still be isomorphic.
Non-split only: d < m. Output lines: "N nmeta m k r d 1" (haar_gen3 argv after N, n = 1).
Usage: enum_nmeta.py LO HI
"""
import sys
from math import gcd

def canon_r(m, k, r):
    best = r
    for u in range(1, k):
        if gcd(u, k) != 1:
            continue
        ru = pow(r, u, m)
        if ru < best:
            best = ru
    return best

def main():
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    for N in range(lo, hi + 1):
        for k in range(2, N + 1):
            if N % k:
                continue
            m = N // k
            if gcd(m, k) == 1:
                continue
            seen = set()
            for r in range(1, m):
                if gcd(r, m) != 1 or pow(r, k, m) != 1 % m:
                    continue
                c = canon_r(m, k, r)
                for d in range(1, m):
                    if m % d:
                        continue
                    if (d * (r - 1)) % m:
                        continue
                    key = (c, d)
                    if key in seen:
                        continue
                    seen.add(key)
                    print(N, "nmeta", m, k, c, d, 1)

if __name__ == "__main__":
    main()
