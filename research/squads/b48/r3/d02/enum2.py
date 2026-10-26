# All meta m k r with m composite, k>=20, N in [2486,2800], r^k=1 mod m, gcd(r-1,m)<=2; ord(r)=faithful flag.
import math
def ordmod(r, m):
    x, t = r % m, 1
    while x != 1 % m:
        x = x * r % m; t += 1
    return t
def composite(m):
    return m > 3 and any(m % d == 0 for d in range(2, int(m**0.5)+1))
rows = []
for m in range(4, 2800):
    if not composite(m): continue
    for k in range(20, 2800 // m + 1):
        N = m * k
        if N < 2486 or N > 2800: continue
        seen = set()
        for r in range(2, m):
            if math.gcd(r, m) != 1 or pow(r, k, m) != 1 % m: continue
            o = ordmod(r, m)
            sub = frozenset(pow(r, t, m) for t in range(o))
            if sub in seen: continue
            seen.add(sub)
            g = math.gcd(r - 1, m)
            rows.append((N, m, k, r, o, g, 'F' if o == k else 'nonfaithful'))
rows.sort()
for row in rows: print(*row)
print(len(rows))
