#!/usr/bin/env python3
"""Direct products of two split metacyclic groups (non-metacyclic in general), of order N in [LO, HI].
Output lines: "N prod meta m1 k1 r1 meta m2 k2 r2 1" (haar_gen3 argv after N, n = 1).
Factors: canonical split metacyclic groups from enum_meta.canon. Unordered pairs (A, B), N1 <= N2.
Usage: enum_prod.py LO HI [MINF]   (MINF: smallest factor order, default 3)
"""
import os, sys
from math import gcd
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from enum_meta import canon

def metas(n):
    out = []
    for k in range(1, n + 1):
        if n % k:
            continue
        m = n // k
        seen = set()
        for r in range(1, m):
            if gcd(r, m) != 1 or pow(r, k, m) != 1 % m:
                continue
            c = canon(m, k, r)
            if c in seen:
                continue
            seen.add(c)
            out.append((m, k, c))
    return out

def main():
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    minf = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    cache = {}
    def M(n):
        if n not in cache:
            cache[n] = metas(n)
        return cache[n]
    for N in range(lo, hi + 1):
        for n1 in range(minf, N // 2 + 1):
            if N % n1:
                continue
            n2 = N // n1
            if n2 < n1:
                continue
            for (m1, k1, r1) in M(n1):
                for (m2, k2, r2) in M(n2):
                    if n1 == n2 and (m2, k2, r2) < (m1, k1, r1):
                        continue
                    print(N, "prod", "meta", m1, k1, r1, "meta", m2, k2, r2, 1)

if __name__ == "__main__":
    main()
