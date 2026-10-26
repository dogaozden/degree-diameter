# Enumerate metacyclic groups Z_m x|_r Z_k of order N in [LO,HI] (r^k = 1 mod m), dedupe by a cheap invariant.
import sys
from math import gcd
LO, HI = int(sys.argv[1]), int(sys.argv[2])
def mul(x, y, m, k, r):
    a, j = x % m, x // m          # index a + m*j
    b, l = y % m, y // m
    rj = pow(r, j, m)
    return ((a + rj * b) % m) + m * ((j + l) % k)
out = []
for N in range(LO, HI + 1):
    if all(N % p for p in range(2, int(N ** .5) + 1)):
        continue  # prime
    seen = {}
    for m in range(1, N + 1):
        if N % m:
            continue
        k = N // m
        for r in range(1, m + 1 if m > 1 else 2):
            if gcd(r, m) != 1 and m > 1:
                continue
            if pow(r, k, m) != 1 % m:
                continue
            if m == 1 and r != 1:
                continue
            # invariant: order multiset, centre size, abelian flag
            def ordr(x):
                o, y = 1, x
                while y != 0:
                    y = mul(y, x, m, k, r); o += 1
                return o
            # identity index 0
            ords = [ordr(x) for x in range(N)]
            inv = sorted(ords)
            # centre: x such that x*y == y*x for all y
            cen = 0
            for x in range(N):
                if all(mul(x, y, m, k, r) == mul(y, x, m, k, r) for y in range(N)):
                    cen += 1
            ab = cen == N
            key = (tuple(sorted(__import__('collections').Counter(ords).items())), cen)
            if ab:
                continue  # skip abelian
            if key in seen:
                continue
            seen[key] = (m, k, r)
            out.append((N, m, k, r, cen))
for N, m, k, r, cen in out:
    print(f"{N} meta:{m}:{k}:{r} centre={cen}")
print(len(out), file=sys.stderr)
