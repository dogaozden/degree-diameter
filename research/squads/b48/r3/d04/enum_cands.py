# enumerate metacyclic Z_m x|_r Z_k, k in 6..11, N=m*k in [2486,2800], ord(r)=k, gcd(r-1,m)<=2
# up to changing generator of Z_k (r -> r^u, u unit mod k): keep canonical (min) r per subgroup
from math import gcd
out = []
for k in range(6, 12):
    units = [u for u in range(1, k) if gcd(u, k) == 1]
    for m in range(2486 // k, 2800 // k + 2):
        N = m * k
        if N < 2486 or N > 2800:
            continue
        seen = set()
        for r in range(2, m):
            if gcd(r, m) != 1:
                continue
            # order of r mod m
            if pow(r, k, m) != 1 % m:
                continue
            # exact order k
            ordr = None
            x = 1
            for t in range(1, k + 1):
                x = x * r % m
                if x == 1 % m:
                    ordr = t
                    break
            if ordr != k:
                continue
            if gcd((r - 1) % m, m) > 2 and gcd(r - 1, m) > 2:
                continue
            if gcd(r - 1, m) > 2:
                continue
            # canonical rep of <r>
            cl = set()
            for u in units:
                rr = pow(r, u, m)
                cl.add(rr)
            canon = min(cl)
            if canon in seen:
                continue
            seen.add(canon)
            # also dedupe r vs canon: keep canon only
            if r != canon:
                continue
            out.append((N, m, k, r, gcd(r - 1, m)))
out.sort()
for row in out:
    print(*row)
print("count", len(out))
