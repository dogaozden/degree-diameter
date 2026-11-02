# Metacyclic groups Z_m x|_r Z_k2 (order K = m*k2, r^k2 = 1 mod m, r != 1 for nonabelian).
# Element (x,y) -> index x*k2+y, identity 0. Writes GROUPFILE: "K" then K*K table entries.
# Usage: mkgroups.py OUTDIR K1 K2 ...   (cyclic groups written as Z<K>)
import sys, os, math
from itertools import product
out = sys.argv[1]; os.makedirs(out, exist_ok=True)
orders = [int(a) for a in sys.argv[2:]]
def table(m, k2, r):
    K = m * k2
    mul = [0] * (K * K)
    for x1, y1, x2, y2 in product(range(m), range(k2), range(m), range(k2)):
        x = (x1 + pow(r, y1, m) * x2) % m; y = (y1 + y2) % k2
        mul[(x1 * k2 + y1) * K + (x2 * k2 + y2)] = x * k2 + y
    return mul
def write(name, K, mul):
    with open(os.path.join(out, name + ".grp"), "w") as f:
        f.write(f"{K}\n" + " ".join(map(str, mul)) + "\n")
index = []
for K in orders:
    write(f"Z{K}", K, table(K, 1, 1))
    index.append((f"Z{K}", K, 1, 1))
    seen = set()
    for m in range(2, K + 1):
        if K % m: continue
        k2 = K // m
        for r in range(2, m):
            if math.gcd(r, m) != 1 or pow(r, k2, m) != 1: continue
            H = frozenset(pow(r, i, m) for i in range(k2))
            key = (m, k2, H)
            if key in seen: continue
            seen.add(key)
            name = f"M{K}_m{m}_k{k2}_r{r}"
            write(name, K, table(m, k2, r))
            index.append((name, m, k2, r))
with open(os.path.join(out, "INDEX.txt"), "w") as f:
    for row in index: f.write("%s m=%d k2=%d r=%d\n" % row)
print(len(index), "groups written")
