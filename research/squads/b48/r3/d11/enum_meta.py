# Enumerate metacyclic groups meta:m:k:r (Z_m x| Z_k, r of order exactly k mod m) with N = m*k in [LO, HI].
# Dedupe r up to powers coprime to k. Count involutions. Prints: spec N inv
import sys, math
from functools import reduce
LO, HI = int(sys.argv[1]), int(sys.argv[2])
def order_mod(r, m):
    if math.gcd(r, m) != 1: return None
    x, o = r % m, 1
    while x != 1 % m:
        x = x * r % m; o += 1
        if o > 10**6: return None
    return o
def involutions(m, k, r):
    rp = [1 % m]
    for j in range(1, k): rp.append(rp[-1] * r % m)
    cnt = 0
    for j in range(k):
        if (2 * j) % k: continue
        for a in range(m):
            if (a + rp[j] * a) % m == 0 and not (j == 0 and a == 0):
                cnt += 1
    return cnt
out = []
for N in range(LO, HI + 1):
    for k in range(2, N + 1):
        if N % k: continue
        m = N // k
        if m < 2: continue
        seen = set()
        for r in range(2, m) if m > 2 else []:
            if math.gcd(r, m) != 1: continue
            if order_mod(r, m) != k: continue
            # canonical: min over r^j with gcd(j,k)=1
            cls = []
            x = r
            for j in range(1, k + 1):
                if math.gcd(j, k) == 1: cls.append(pow(r, j, m))
            c = min(cls)
            if c in seen: continue
            seen.add(c)
            out.append((N, m, k, c, involutions(m, k, c)))
for N, m, k, r, inv in out:
    print("meta:%d:%d:%d" % (m, k, r), N, inv, "fraction_inv=%.4f" % (inv / N))
