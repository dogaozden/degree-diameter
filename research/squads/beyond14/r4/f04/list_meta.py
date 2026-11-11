import sys
from math import gcd
lo, hi = int(sys.argv[1]), int(sys.argv[2])
out = []
for N in range(lo, hi + 1):
    for k in range(4, N // 4 + 1):
        if N % k: continue
        m = N // k
        if m < 3: continue
        for r in range(2, m):
            if gcd(r, m) != 1 or pow(r, k, m) != 1: continue
            if any(pow(r, j, m) == 1 for j in range(1, k)): continue
            fpf = int(all(gcd(pow(r, j, m) - 1, m) == 1 for j in range(1, k)))
            out.append((fpf, k, N, m, r))
            break
for fpf, k, N, m, r in sorted(out, key=lambda t: (-t[0], -t[1])):
    if k >= 6: print(N, m, k, r, fpf)
