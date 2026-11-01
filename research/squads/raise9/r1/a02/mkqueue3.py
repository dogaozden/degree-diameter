import math, collections
def order_mod(r, m):
    if math.gcd(r, m) != 1: return 0
    x, o = r % m, 1
    while x != 1 % m:
        x = x * r % m; o += 1
        if o > m: return 0
    return o
# nonabelian metacyclic small groups: (order, spec)
small = []
for n in range(6, 83):
    for k in range(2, n + 1):
        if n % k: continue
        m = n // k
        if m < 2: continue
        seen = set()
        for r in range(2, m):
            if math.gcd(r, m) != 1 or pow(r, k, m) != 1 % m: continue
            key = min(pow(r, j, m) for j in range(1, k + 1) if math.gcd(j, k) == 1)
            if key in seen: continue
            seen.add(key)
            small.append((n, f"meta {m} {k} {key}"))
small.append((6, "dih 3")); 
small = sorted(set(small))
out = []
for N in range(254, 331):
    for a, sa in small:
        if N % a: continue
        b = N // a
        if b < 2: continue
        out.append(f"{sa} x cyc {b}")
        # products with dihedral-type small nonabelian partner of order b... (b must be order of a meta)
for a, sa in small:
    for b, sb in small:
        if a > b: continue
        if 254 <= a * b <= 330 and not (a == b and sa == sb):
            out.append(f"{sa} x {sb}")
out = sorted(set(out))
open("queue3.txt", "w").write("\n".join(out) + "\n")
print(len(out), len(small), file=__import__('sys').stderr)
