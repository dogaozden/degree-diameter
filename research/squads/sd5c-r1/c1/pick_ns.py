# Filter the non-split candidates: moderate k (8..60), m >= 50, every valid s listed (s != 0, (r-1)s = 0 mod m).
from math import gcd
lo, hi = 5851, 6100
rows = []
for N in range(lo, hi + 1):
    for m in range(50, N + 1):
        if N % m: continue
        k = N // m
        if not (8 <= k <= 60): continue
        for r in range(2, m):
            if gcd(r, m) != 1 or pow(r, k, m) != 1 % m: continue
            for s in range(1, m):
                if (r * s - s) % m == 0:
                    rows.append((N, m, k, r, s, m // gcd(s, m), gcd(r - 1, m)))
print(len(rows))
# prefer s of order 2 (s = m/2, m even, r odd) and a spread of (m,k)
for row in rows:
    N, m, k, r, s, o, g = row
    if o == 2:
        print("N=%d m=%d k=%d r=%d s=%d ord(s)=%d gcd(r-1,m)=%d" % row)
