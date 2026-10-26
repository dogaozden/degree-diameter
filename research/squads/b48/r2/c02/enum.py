import sys, math
from math import gcd
lo, hi, minord = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
out = []
for N in range(lo, hi + 1):
    for k in range(2, N + 1):
        if N % k: continue
        m = N // k
        if m < 2: continue
        for r in range(2, m):
            if gcd(r, m) != 1: continue
            # order of r mod m
            o, x = 1, r % m
            while x != 1:
                x = x * r % m; o += 1
                if o > k: break
            if o > k or k % o: continue
            if o < minord: continue
            # r^k == 1 already since o | k
            # skip if r is not the minimal representative of its <r>-subgroup generator class (cheap dedupe)
            gens = set()
            for e in range(1, o):
                if gcd(e, o) == 1:
                    gens.add(pow(r, e, m))
            if min(gens) != r: continue
            out.append((N, m, k, r, o))
for N, m, k, r, o in out:
    print(f"meta:{m}:{k}:{r} {N} ord={o}")
