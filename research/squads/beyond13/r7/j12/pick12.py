#!/usr/bin/env python3
# pick12.py d D Nlo Nhi kmin kmax : odd m, odd k (k composite or prime), N = m*k in [Nlo,Nhi], r nontrivial with r^k = 1 mod m
import sys, math
def W(d, D):
    if D % 2 == 0: return sum(d * (d - 1) ** (2 * i) for i in range(D // 2))
    return 1 + sum(d * (d - 1) ** (2 * i - 1) for i in range(1, (D - 1) // 2 + 1))
d, D, lo, hi, kmin, kmax = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6])
w = W(d, D); out = []
for k in range(kmin | 1, kmax + 1, 2):
    m = (lo // k) | 1
    while m * k <= hi:
        if m * k >= lo and m > 1 and math.gcd(m, k) == 1 or (m*k>=lo and math.gcd(m,k)>1):
            # r of order dividing k, nontrivial, gcd(r,m)=1
            r = None
            for cand in range(2, min(m, 5000)):
                if math.gcd(cand, m) == 1 and pow(cand, k, m) == 1:
                    r = cand; break
            if r is not None:
                N = m * k
                out.append((N * math.exp(-w / N), m, k, r, N))
        m += 2
out.sort()
for mu, m, k, r, N in out[:int(sys.argv[7]) if len(sys.argv) > 7 else 40]:
    print(m, k, r, N, f"mu={mu:.2f}")
