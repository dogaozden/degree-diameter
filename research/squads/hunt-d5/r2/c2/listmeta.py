# list metacyclic groups Z_m x|_r Z_k of order N in [689,710], nonabelian, r^k = 1 mod m, one r per subgroup <r>
from math import gcd
out = []
for N in range(689, 711):
    for k in range(2, N):
        if N % k: continue
        m = N // k
        if m < 2: continue
        units = [r for r in range(2, m) if gcd(r, m) == 1] if m > 2 else []
        seen = set()
        for r in units:
            if pow(r, k, m) != 1: continue
            sub = frozenset(pow(r, j, m) for j in range(k))
            if sub in seen: continue
            seen.add(sub)
            d = 1; x = r
            while x != 1: x = x * r % m; d += 1
            if d == 1: continue
            out.append((N, m, k, r, d))
# keep nonabelian only (r != 1 already); print
for t in out: print("meta:%d:%d:%d N=%d order_r=%d" % (t[1], t[2], t[3], t[0], t[4]))
print("total", len(out))
