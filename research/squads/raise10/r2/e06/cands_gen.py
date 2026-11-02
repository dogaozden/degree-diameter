import json
from math import gcd

cands = []
for k in range(16, 49, 2):
    mlo = -(-47737 // k)
    mhi = 48400 // k
    for m in range(mlo, mhi + 1):
        if m < 3:
            continue
        good = []
        for r in range(2, m):
            if gcd(r, m) == 1 and pow(r, k, m) == 1:
                good.append(r)
        if good:
            cands.append((m * k, m, k, good))

out = [(N, m, k, len(g), g[:8]) for (N, m, k, g) in sorted(cands)]
json.dump(out, open('/home/user/degree-diameter/research/squads/raise10/r2/e06/cands.json', 'w'))
print("groups with some r:", len(cands), "r options:", sum(len(c[3]) for c in cands))
for x in out[:12]:
    print(x)
