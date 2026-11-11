# Enumerate split metacyclic Z_m x|_r Z_k with m*k in 2440..2485, d = ord(r mod m) >= 8, r^k = 1 mod m,
# dedup r ~ r^t (gcd(t,k)=1), keep |G/G'| = k*gcd(r-1,m) <= 309.  Writes cands.json (sorted by d desc).
import json
from math import gcd
def order_mod(r, m):
    x = r % m; d = 1
    while x != 1 % m:
        x = x * r % m; d += 1
    return d
rows = []
allrows = 0
for N in range(2440, 2486):
    for m in range(2, N + 1):
        if N % m: continue
        k = N // m
        seen = set()
        for r in range(2, m):
            if gcd(r, m) != 1 or pow(r, k, m) != 1 % m: continue
            d = order_mod(r, m)
            if d < 8: continue
            canon = min(pow(r, t, m) for t in range(1, k + 1) if gcd(t, k) == 1)
            if canon in seen: continue
            seen.add(canon)
            allrows += 1
            q = k * gcd(r - 1, m)
            rows.append(dict(N=N, m=m, k=k, r=canon, d=d, q=q, keep=q <= 309))
rows.sort(key=lambda t: (-t['d'], t['N'], t['m']))
json.dump(rows, open('cands.json', 'w'), indent=0)
keep = [t for t in rows if t['keep']]
print('all (d>=8, deduped by r~r^t):', len(rows), ' kept (|G/G\'|<=309):', len(keep))
from collections import Counter
print(sorted(Counter(t['N'] for t in keep).items()))
for t in keep:
    print(t['N'], 'm', t['m'], 'k', t['k'], 'r', t['r'], 'd', t['d'], 'q', t['q'])
