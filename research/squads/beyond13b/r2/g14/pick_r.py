#!/usr/bin/env python3
"""pick_r.py m k [n] [seed]: up to n distinct isomorphism classes of r (order exactly k, gcd(r-1,m)=1) for
Z_m x|_r Z_k, classes taken as {r^j : j in (Z/k)^*}; prints the minimal representative of each class sampled."""
import sys, random, math
m, k = int(sys.argv[1]), int(sys.argv[2]); n = int(sys.argv[3]) if len(sys.argv) > 3 else 5
seed = int(sys.argv[4]) if len(sys.argv) > 4 else 1
# elements of order k in (Z/m)^*: x with x^k = 1, x != 1 mod each prime power (checked by brute force on units of order | k)
units = [x for x in range(2, m) if math.gcd(x, m) == 1 and pow(x, k, m) == 1]
ok = []
for x in units:
    if math.gcd(x - 1, m) != 1: continue
    # order exactly k: since k prime, any x != 1 with x^k=1 has order k
    ok.append(x)
seen = set(); classes = []
for x in ok:
    c = min(pow(x, j, m) for j in range(1, k) if math.gcd(j, k) == 1)
    if c not in seen: seen.add(c); classes.append(c)
rng = random.Random(seed); rng.shuffle(classes)
print(f"# m={m} k={k} classes={len(classes)}", file=sys.stderr)
for c in classes[:n]: print(c)
