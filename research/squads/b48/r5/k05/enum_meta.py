# enumerate metacyclic Z_m x|_r Z_k (k even, order m*k in [LO,HI]) up to r -> r^u (u unit mod k)
import sys, math
LO, HI = int(sys.argv[1]), int(sys.argv[2])
out = []
for N in range(LO, HI + 1):
    for k in range(2, N + 1, 2):
        if N % k: continue
        m = N // k
        seen = set()
        for r in range(0, m if m > 1 else 1):
            if m == 1:
                rr = 0
            else:
                rr = r
            if pow(rr, k, m) != (1 % m): continue
            if m > 1 and math.gcd(rr, m) != 1: continue
            # orbit under units of k
            orb = min(pow(rr, u, m) if m > 1 else 0 for u in range(1, k + 1) if math.gcd(u, k) == 1)
            if orb in seen: continue
            seen.add(orb)
            out.append((N, m, k, orb))
for N, m, k, r in out:
    print(N, m, k, r)
