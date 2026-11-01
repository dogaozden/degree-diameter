import sys, random
from shapes import metas
lo, hi = 1620000, 1800000
big = [x for x in metas(7*1000, 2*10**6, ) if x[1] >= 11 and x[1] <= 60]
print("meta k>=11 entries with m*k in [7000,2e6]:", len(big), file=sys.stderr)
# metacyclic x Z_n: k in 11..60, n prime in {7,13,19,31}
for n in (7, 13, 19, 31):
    c = [x for x in metas(lo // n, hi // n) if x[1] >= 11]
    c.sort(key=lambda t: abs(t[0]*t[1]*n - 1710000))
    for m, k, r in c[:3]:
        print(f"META n={n} meta {m} {k} {r} n {n} N={m*k*n}")
# products of two metas (k in 11..60), order m1k1*m2k2 in range, n=1
small = [x for x in metas(900, 1900) if x[1] >= 11]
ords = {}
for m, k, r in small:
    ords.setdefault(m*k, []).append((m, k, r))
cnt = 0
for o1 in sorted(ords):
    for o2 in sorted(ords):
        if o1 > o2: continue
        N = o1 * o2
        if lo <= N <= hi and ords[o1] and ords[o2]:
            a = ords[o1][0]; b = ords[o2][0]
            print(f"PROD {a[0]} {a[1]} {a[2]} {b[0]} {b[1]} {b[2]} N={N}")
            cnt += 1
            if cnt >= 12: sys.exit()
