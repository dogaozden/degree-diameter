"""List metacyclic groups Z_m x|_r Z_k (r^k = 1 mod m, canonical up to Aut(Z_k)) with N = m*k in [lo, hi]."""
import sys, math
lo, hi = int(sys.argv[1]), int(sys.argv[2])
out = []
for k in range(2, 200):
    for m in range(3, hi // k + 1):
        N = m * k
        if N < lo or N > hi:
            continue
        seen = set()
        for r in range(1, m):
            if math.gcd(r, m) != 1 or pow(r, k, m) != 1 % m:
                continue
            canon = min(pow(r, u, m) for u in range(1, k + 1) if math.gcd(u, k) == 1)
            if canon in seen:
                continue
            seen.add(canon)
            out.append((N, m, k, canon))
out.sort(key=lambda t: -t[0])
for N, m, k, r in out:
    print(N, m, k, r)
