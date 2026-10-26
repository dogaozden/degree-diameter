# Enumerate metacyclic Z_m x|_r Z_k, m composite, k>=20, N=m*k in [2486,2800], ord_m(r)=k, gcd(r-1,m) in {1,2}.
import math, sys
def ordmod(r, m):
    if math.gcd(r, m) != 1: return None
    x, t = r % m, 1
    if m == 1: return 1
    while x != 1:
        x = x * r % m; t += 1
    return t
def composite(m):
    return m > 3 and any(m % d == 0 for d in range(2, int(m**0.5)+1))
out = []
for m in range(2, 2800):
    if not composite(m): continue
    for k in range(20, 2800 // m + 1):
        N = m * k
        if N < 2486 or N > 2800: continue
        seen = set()
        for r in range(2, m):
            if math.gcd(r, m) != 1: continue
            if ordmod(r, m) != k: continue
            sub = frozenset(pow(r, t, m) for t in range(k))  # cyclic subgroup, one per class
            if sub in seen: continue
            seen.add(sub)
            g = math.gcd(r - 1, m)
            if g > 2: continue
            out.append((N, m, k, r, g, sum(1 for x in sub if (x*x) % m == 1 and x != 1) ))
out.sort()
for row in out: print(*row)
print(len(out), file=sys.stderr)
