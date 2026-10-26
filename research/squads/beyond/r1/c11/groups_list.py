"""List metacyclic groups Z_m x|_r Z_k of order N with r^k = 1 mod m (r unit mod m). Prints 'm k r' lines.
Usage: python3 groups_list.py N [mink]"""
import sys
from math import gcd
N = int(sys.argv[1])
for k in range(1, N + 1):
    if N % k:
        continue
    m = N // k
    if m < 1:
        continue
    seen = set()
    for r in range(1, m + 1) if m > 1 else [0]:
        if m > 1 and gcd(r, m) != 1:
            continue
        if pow(r, k, m) != (1 % m):
            continue
        # canonical: skip r with same subgroup generated? keep all distinct r for simplicity
        print(m, k, r if m > 1 else 1)
