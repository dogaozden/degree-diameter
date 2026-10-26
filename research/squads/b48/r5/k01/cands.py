# candidate meta groups Z_m x|_r Z_k with k = 2 mod 4, r^(k/2) = -1 mod m (all j=k/2 elements are odd involutions)
import math
out = []
for k in range(2, 60, 4):
    for m in range(2, 500):
        N = m * k
        if N < 401 or N > 460: continue
        if math.gcd(m, 1) != 1: continue
        for r in range(1, m):
            if math.gcd(r, m) != 1: continue
            if pow(r, k, m) != 1 % m: continue
            if (pow(r, k // 2, m) + 1) % m != 0: continue
            out.append((N, m, k, r))
print(len(out))
import collections
c = collections.Counter((N) for N, *_ in out)
print(sorted(c.items()))
for t in out[:400]:
    pass
import random
random.seed(1)
sel = [t for t in out if t[2] in (2, 6, 10, 14)]
for t in sel[:80]: print(*t)
