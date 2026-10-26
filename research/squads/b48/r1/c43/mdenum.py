import sys
from math import gcd
# enumerate metacyclic Z_m x|_r Z_k (r^k = 1 mod m, gcd(r,m)=1), classes r ~ r^j (gcd(j,k)=1)
def ordmod(r, m):
    x, o = r % m, 1
    while x != 1 % m:
        x = x * r % m; o += 1
        if o > 10**6: return None
    return o
def classes(m, k):
    units = [r for r in range(1, m) if gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
    seen = set(); out = []
    for r in units:
        if r in seen: continue
        orb = set()
        for j in range(1, k + 1):
            if gcd(j, k) == 1: orb.add(pow(r, j, m))
        seen |= orb
        out.append(r)
    return out
def groups(N, ks=None, minr=None):
    res = []
    for k in range(2, N):
        if N % k: continue
        m = N // k
        if m < 2: continue
        if ks and k not in ks: continue
        for r in classes(m, k):
            if m == 1: continue
            res.append((m, k, r, ordmod(r, m)))
    return res
if __name__ == "__main__":
    N = int(sys.argv[1]); ks = set(map(int, sys.argv[2].split(','))) if len(sys.argv) > 2 else None
    for m, k, r, o in groups(N, ks):
        print(m, k, r, "ord_r=", o)
