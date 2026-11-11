# List metacyclic groups Z_m x|_r Z_n (r^n = 1 mod m, r != 1 mod m) of order G = m*n, one line per (m, n, r).
# Usage: python3 groups.py G [maxper]   -> prints "m n r" lines (prefers larger orders of r, i.e. more non-abelian)
import sys
from math import gcd
G = int(sys.argv[1]); maxper = int(sys.argv[2]) if len(sys.argv) > 2 else 3
out = []
for m in range(3, G + 1):
    if G % m: continue
    n = G // m
    if n < 2: continue
    cands = []
    for r in range(2, m):
        if gcd(r, m) != 1 or pow(r, n, m) != 1: continue
        d = next(d for d in range(1, n + 1) if pow(r, d, m) == 1)
        if d > 1: cands.append((-d, r))
    cands.sort()
    for _, r in cands[:maxper]: out.append((m, n, r))
for m, n, r in out: print(m, n, r)
