# enum.py: candidate metacyclic groups Z_m x|_r Z_k with N = m*k in [lo,hi], k >= 13, r != 1, r^k = 1 mod m.
# Prints "N m k r ord_r mu" with mu = N exp(-W/N), W for d=5, D=10 (even D).
import sys, math
from math import gcd
lo, hi = int(sys.argv[1]), int(sys.argv[2])
d, D = 5, 10
W = sum(d * (d - 1) ** (2 * i) for i in range(D // 2))
def order(r, m):
    x, e = r % m, 1
    while x != 1:
        x = x * r % m; e += 1
        if e > 10**6: return None
    return e
out = []
for N in range(lo, hi + 1):
    for k in range(13, N + 1):
        if N % k: continue
        m = N // k
        if m < 3: continue
        # collect units r with r^k = 1 mod m, r != 1; one per cyclic subgroup (by smallest generator)
        seen = set(); picks = {}
        units = [r for r in range(2, m) if gcd(r, m) == 1] if m < 4000 else None
        if units is None: continue
        if k % 2 == 1 and m % 2 == 0 or True:
            pass
        for r in units:
            if pow(r, k, m) != 1: continue
            o = order(r, m)
            if o is None or o == 1: continue
            # subgroup id: frozenset of powers
            pw = frozenset(pow(r, t, m) for t in range(o))
            if pw in seen: continue
            seen.add(pw)
            picks.setdefault(o, r)
        for o, r in sorted(picks.items()):
            out.append((N, m, k, r, o))
W_over = W
for N, m, k, r, o in out:
    mu = N * math.exp(-W / N)
    print(N, m, k, r, o, f"{mu:.2f}")
