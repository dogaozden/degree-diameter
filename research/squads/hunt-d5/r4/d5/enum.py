# enumerate metacyclic Z_m x|_r Z_k (m*k = N, r^k = 1 mod m, r != 1), up to k-power equivalence
import sys, math
from math import gcd
def order(r, m):
    x, o = r % m, 1
    while x != 1 % m:
        x = x * r % m; o += 1
        if o > 10**6: return None
    return o
def groups(N):
    out = []
    for k in range(2, N + 1):
        if N % k: continue
        m = N // k
        if m < 3: continue
        seen = set()
        for r in range(2, m):
            if gcd(r, m) != 1: continue
            if pow(r, k, m) != 1 % m: continue
            e = order(r, m)
            if e == 1: continue
            # canonical rep under r -> r^s, gcd(s,k)=1
            orb = {pow(r, s, m) for s in range(1, k + 1) if gcd(s, k) == 1}
            key = min(orb)
            if key in seen: continue
            seen.add(key)
            out.append((m, k, key, e))
    return out
if __name__ == "__main__":
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    for N in range(lo, hi + 1):
        for (m, k, r, e) in groups(N):
            p = [q for q in range(2, m + 1) if m % q == 0 and all(q % t for t in range(2, int(q**0.5) + 1))]
            print(N, m, k, r, e, "maxprime", max(p) if p else 1, "gcd_check", gcd(m, k))
