import math
from itertools import product
existing = {(99,34,3,1),(43,4,7,1),(61,9,5,1),(103,46,3,1),(31,15,10,1),(13,2,24,1),(79,78,4,1),(163,162,2,1),(41,3,8,1),(37,7,9,1)}
out = []
for N in range(297, 321):
    for t in range(1, N+1):
        if N % t: continue
        for k in range(2, N//t+1):
            if (N//t) % k: continue
            m = N//(t*k)
            if m < 2: continue
            units = [r for r in range(1, m) if math.gcd(r, m) == 1] if m > 1 else [0]
            for r in units:
                if r == 1: continue
                if pow(r, k, m) != 1 % m: continue
                # order of r
                o = 1; x = r
                while x != 1 % m: x = x*r % m; o += 1
                out.append((N, m, k, r, t, o))
for row in out:
    N, m, k, r, t, o = row
    if (m,k,r,t) in existing: continue
    print(N, f"Z{m}x|{r}Z{k}xZ{t}", "ord_r", o)
