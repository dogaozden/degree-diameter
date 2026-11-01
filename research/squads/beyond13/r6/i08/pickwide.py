#!/usr/bin/env python3
# pickwide.py d D Nlo Nhi kmin kmax: prime m, any k | m-1 in [kmin,kmax], r = g^((m-1)/k) of order dividing k (r != 1); prints m k r N mu
import sys, math
def W(d, D):
    if D % 2 == 0: return sum(d * (d - 1) ** (2 * i) for i in range(D // 2))
    return 1 + sum(d * (d - 1) ** (2 * i - 1) for i in range(1, (D - 1) // 2 + 1))
def isp(x):
    if x < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if x % p == 0: return x == p
    dd, s = x - 1, 0
    while dd % 2 == 0: dd //= 2; s += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        y = pow(a, dd, x)
        if y in (1, x-1): continue
        for _ in range(s-1):
            y = y*y % x
            if y == x-1: break
        else: return False
    return True
d, D, lo, hi = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
kmin, kmax = int(sys.argv[5]), int(sys.argv[6])
w = W(d, D); out = []
for k in range(kmin, kmax + 1):
    m = lo // k + 1
    while m * k <= hi:
        if m % 2 == 1 and m * k >= lo and isp(m) and (m - 1) % k == 0:
            g = 2
            while pow(g, (m-1)//2, m) == 1 or pow(g, (m-1)//3 if (m-1)%3==0 else 1, m) == 1 and False: g += 1
            r = pow(g, (m-1)//k, m)
            if r != 1 and pow(r, k, m) == 1:
                N = m*k; out.append((N*math.exp(-w/N), m, k, r, N))
        m += 1
out.sort()
for mu, m, k, r, N in out[:int(sys.argv[7]) if len(sys.argv) > 7 else 25]:
    print(m, k, r, N, f"{mu:.2f}")
