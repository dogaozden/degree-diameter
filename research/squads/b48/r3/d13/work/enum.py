# enumerate metacyclic Z_m x|_r Z_k with order N in [2486, 2600]; count involutions analytically
import math, sys
res = []
for N in range(2486, 2601):
    for k in range(3, N):
        if N % k: continue
        m = N // k
        if m < 3: continue
        for r in range(2, m):
            if math.gcd(r, m) != 1: continue
            if pow(r, k, m) != 1 % m: continue
            # faithful-ish: gcd(r-1,m)=1 preferred (exh_meta requirement) -- record flag
            inv = 0
            for j in range(k):
                if (2*j) % k == 0:
                    inv += math.gcd((1 + pow(r, j, m)) % m, m) if m > 1 else 1
            inv -= 1
            res.append((N, m, k, r, inv, math.gcd(r-1, m)))
# summary: odd order groups (inv=0) and few-involution groups
import collections
odd = [x for x in res if x[4] == 0]
print("odd-order (no involutions) count:", len(odd))
for x in odd[:80]:
    print("N=%d m=%d k=%d r=%d inv=%d gcd(r-1,m)=%d" % x)
