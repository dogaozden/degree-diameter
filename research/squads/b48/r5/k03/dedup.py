# keep one r per (m,k) orbit under r -> r^s, s a unit mod k (same group up to iso)
import sys
from math import gcd
from collections import defaultdict
seen = {}
out = []
for line in open('groups.txt'):
    N, m, k, r = map(int, line.split())
    units = [s for s in range(1, k + 1) if gcd(s, k) == 1] if k > 1 else [1]
    canon = min(pow(r, s, m) if m > 1 else 0 for s in units)
    key = (N, m, k, canon)
    if key in seen: continue
    seen[key] = 1
    out.append((N, m, k, canon))
print(len(out))
with open('groups_red.txt', 'w') as f:
    for N, m, k, r in out: f.write(f"{N} {m} {k} {r}\n")
