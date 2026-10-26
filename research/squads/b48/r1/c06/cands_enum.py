# Enumerate non-faithful metacyclic groups meta m k r = Z_m x| Z_k with ord(r) a proper divisor d>1 of k.
# Up to isomorphism: r ~ r^j for j a unit mod k (the generator of Z_k changes). Also m in Z_m^*.
from math import gcd
out = []
for N in range(1094, 1201):
    for k in range(4, 61):
        if N % k: continue
        m = N // k
        if m < 2: continue
        seen = set()
        for r in range(2, m):
            if gcd(r, m) != 1: continue
            if pow(r, k, m) != 1: continue
            # order of r mod m
            d = 1; x = r % m
            while x != 1:
                x = x * r % m; d += 1
            if d <= 1 or k % d != 0 or d == k: continue
            # canonical rep under r -> r^j, j unit mod k
            orb = min(pow(r, j, m) for j in range(1, k) if gcd(j, k) == 1)
            if orb in seen: continue
            seen.add(orb)
            out.append((N, m, k, r, d))
for row in out:
    print(*row)
print(len(out), file=__import__('sys').stderr)
