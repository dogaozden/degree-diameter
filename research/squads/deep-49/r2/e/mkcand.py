# card r2e: split metacyclic Z_m x|_r Z_k for the orders 2531..2600 that GAP's SmallGroups library does not have.
# Same filters as r1/c2/mkcand.py: dedupe r ~ r^t (gcd(t,k)=1), d = ord(r mod m) >= 3, |G/G'| = k*gcd(r-1,m) <= 309.
import json
from math import gcd
Ns = [2532, 2535, 2536, 2538, 2540, 2541, 2544, 2548, 2550, 2552, 2556, 2560, 2562, 2565, 2568, 2574, 2576,
      2580, 2583, 2584, 2590, 2592, 2596, 2600]
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
json.dump(rows, open('/home/user/degree-diameter/research/squads/deep-49/r2/e/candidates.json', 'w'), indent=0)
keep = [t for t in rows if t['keep']]
print('all', len(rows), 'kept (q<=309)', len(keep))
from collections import Counter
print(sorted(Counter(t['N'] for t in keep).items()))
print('d>=3 kept list:')
for t in keep:
    print(t['N'], t['m'], t['k'], t['r'], 'd', t['d'], 'q', t['q'])
