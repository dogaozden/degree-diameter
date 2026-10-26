# Enumerate metacyclic groups Z_m x|_r Z_k with N = m*k in [2486, 2800], k in [12, 19],
# d = ord(r mod m) >= 6, d | k, gcd(r-1, m) <= 2. One r per cyclic subgroup of units (isomorphism class).
from math import gcd
out = []
for k in range(12, 20):
    for m in range(2, 2800):
        N = m * k
        if N < 2486 or N > 2800 or m % 1:
            continue
        seen = set()
        for r in range(2, m):
            if gcd(r, m) != 1:
                continue
            if gcd(r - 1, m) > 2:
                continue
            # order of r mod m
            d, x = 1, r
            while x != 1 % m:
                x = x * r % m
                d += 1
                if d > k:
                    break
            if d > k or k % d != 0 or d < 6:
                continue
            cyc = frozenset(pow(r, i, m) for i in range(d))
            if cyc in seen:
                continue
            seen.add(cyc)
            out.append((m, k, r, d, N, gcd(r - 1, m)))
for t in sorted(out, key=lambda t: (t[4], t[1])):
    print(*t)
print(len(out), file=__import__('sys').stderr)
