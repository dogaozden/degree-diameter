import sys
LO, HI = 1762650, 1800000
def isp(x):
    if x < 2: return False
    i = 2
    while i * i <= x:
        if x % i == 0: return False
        i += 1
    return True
# metacyclic Z_m x|_r Z_k, m prime odd, k | m-1, k >= 2 (r of order k exists since m prime)
meta = []
for m in range(3, 2000000 // 2):
    if m % 2 == 0 or not isp(m): continue
    for k in range(2, 200):
        if (m - 1) % k: continue
        if m * k > 1000000: break
        meta.append((m * k, m, k))
meta.sort()
# single factor sizes near window divided by small n
out = []
# two-factor products, N1 <= N2
import bisect
sizes = [x[0] for x in meta]
for a in meta:
    if a[0] > 1400000: break
    lo = max(LO // a[0] + 1, a[0])
    for b in meta:
        if b[0] < a[0]: continue
        N = a[0] * b[0]
        if N > HI: break
        if N >= LO and N <= HI and (N > 0):
            out.append((N, a, b))
out.sort()
print("two-factor products (N, (N1,m,k), (N2,m',k')):", len(out))
for o in out[:80]:
    print(o)
# single meta times Z_n: N = m*k*n, n prime (n=1 or prime)
sing = []
for a in meta:
    for n in range(2, HI // a[0] + 1):
        if isp(n) and LO <= a[0] * n <= HI:
            sing.append((a[0] * n, a, n))
print("single meta x Z_n:", len(sing))
for s in sorted(sing)[:40]: print(s)
