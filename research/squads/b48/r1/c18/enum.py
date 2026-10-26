# enumerate metacyclic Z_m x|_r Z_k, order N in [547,600], k in KS, r != 1 unit with r^k = 1 mod m
# classes: r ~ r^j with gcd(j,k)=1 (keeps the same group up to relabelling the Z_k generator)
import math, sys
KS = [4, 6, 8, 10, 12, 20, 24]
out = []
seen = set()
for N in range(547, 601):
    for k in KS:
        if N % k: continue
        m = N // k
        if m < 2: continue
        for r in range(2, m):
            if math.gcd(r, m) != 1: continue
            if pow(r, k, m) != 1: continue
            if (r - 1) % m == 0: continue
            # order of r mod m
            o = 1; x = r
            while x != 1: x = x * r % m; o += 1
            # class under r -> r^j, gcd(j,k)=1
            cls = min(pow(r, j, m) for j in range(1, k + 1) if math.gcd(j, k) == 1 and math.gcd(j, k) == 1)
            key = (m, k, cls)
            if key in seen: continue
            seen.add(key)
            out.append((N, m, k, r, o, cls))
for t in out: print("N=%d meta:%d:%d:%d ord_r=%d class_min_r=%d" % (t[0], t[1], t[2], t[3], t[4], t[5]))
print(len(out), file=sys.stderr)
