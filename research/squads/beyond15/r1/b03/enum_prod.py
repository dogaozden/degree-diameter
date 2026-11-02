#!/usr/bin/env python3
"""enum_prod.py: pairs of odd-order Frobenius groups Z_m x|_r Z_k (k>=5 odd prime, m prime = 1 mod k) whose product
order N = |G1| |G2| lies in [lo, hi]; prints "N  m1 k1 r1 N1  m2 k2 r2 N2" and mu (d=4, D=15)."""
import sys, math
sys.path.insert(0, '/home/user/degree-diameter/research/frontier/beyond13/meta')
def isp(x):
    if x < 2: return False
    i = 2
    while i * i <= x:
        if x % i == 0: return False
        i += 1
    return True
def W(d, D):
    if D % 2 == 0: return sum(d * (d - 1) ** (2 * i) for i in range(D // 2))
    return 1 + sum(d * (d - 1) ** (2 * i - 1) for i in range(1, (D - 1) // 2 + 1))
d, D, lo, hi = 4, 15, 660000, 700000
if len(sys.argv) > 2: lo, hi = int(sys.argv[1]), int(sys.argv[2])
def prim_root_order(m, k):
    # element r of exact order k mod m
    for g in range(2, m):
        r = pow(g, (m - 1) // k, m)
        if r != 1: return r
groups = []
for k in [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]:
    m = 2 * k + 1
    while m * k <= hi // 5:
        if isp(m):
            groups.append((m * k, m, k, prim_root_order(m, k)))
        m += 2 * k
groups.sort()
w = W(d, D)
out = []
for i, (N1, m1, k1, r1) in enumerate(groups):
    for (N2, m2, k2, r2) in groups[i:]:
        N = N1 * N2
        if lo <= N <= hi:
            out.append((N, m1, k1, r1, N1, m2, k2, r2, N2))
for row in out:
    N = row[0]
    print(N, f"{N*math.exp(-w/N):.2f}", "meta", row[1], row[2], row[3], "meta", row[5], row[6], row[7], "|", row[4], row[8])
print("count", len(out), "W", w, file=sys.stderr)
