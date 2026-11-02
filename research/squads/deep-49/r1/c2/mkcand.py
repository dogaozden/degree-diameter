# Enumerate split metacyclic groups Z_m x|_r Z_k of the target orders (dedup r ~ r^t, t unit mod k).
# Filters from cards.md: d = ord(r mod m) >= 3, |G/G'| = k*gcd(r-1,m) <= 309.
import json
from math import gcd
Ns = [2488, 2490, 2492, 2496, 2499, 2500, 2502, 2504, 2508, 2511, 2512, 2516, 2520, 2528, 2530]
def order_mod(r, m):
    x = r % m; d = 1
    while x != 1 % m:
        x = x * r % m; d += 1
    return d
rows = []
for N in Ns:
    for m in range(2, N + 1):
        if N % m: continue
        k = N // m
        seen = set()
        for r in range(2, m):
            if gcd(r, m) != 1 or pow(r, k, m) != 1 % m: continue
            d = order_mod(r, m)
            if d < 3: continue
            canon = min(pow(r, t, m) for t in range(1, k + 1) if gcd(t, k) == 1)
            if canon in seen: continue
            seen.add(canon)
            q = k * gcd(r - 1, m)
            rows.append(dict(N=N, m=m, k=k, r=canon, d=d, q=q, keep=q <= 309))
rows.sort(key=lambda t: (-t['d'], t['N']))
json.dump(rows, open('/home/user/degree-diameter/research/squads/deep-49/r1/c2/candidates.json', 'w'), indent=0)
keep = [t for t in rows if t['keep']]
print('all', len(rows), 'kept (q<=309)', len(keep))
for t in keep:
    print(t['N'], t['m'], t['k'], t['r'], 'd', t['d'], 'q', t['q'])
