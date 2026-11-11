import sys
from math import gcd
lo, hi, kmin = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
def order(r, m):
    x, d = r % m, 1
    while x != 1 % m:
        x = x * r % m; d += 1
        if d > m: return 0
    return d
for N in range(lo, hi + 1):
    for k in range(kmin, N // 3 + 1):
        if N % k: continue
        m = N // k
        if m < 4: continue
        ts = [t for t in range(2, m) if gcd(t, m) == 1 and pow(t, 3, m) == 1 % m]
        if not ts: continue
        seen = set()
        for r in range(2, m):
            if gcd(r, m) != 1: continue
            d = order(r, m)
            if d < 2 or k % d: continue
            sub = frozenset(pow(r, j, m) for j in range(d))
            if sub in seen: continue
            seen.add(sub)
            print(N, m, k, r, d, ts[0])
