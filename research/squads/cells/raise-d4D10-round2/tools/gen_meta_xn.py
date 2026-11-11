"""Metacyclic x Z_n families (n >= 2) of order in [lo, hi], haar_gen3 spec 'meta m k r n' (+ 'pgl/...' not here).
Groups Z_m x|_r Z_k (r != 1, r^k = 1 mod m, <r> deduplicated) times Z_n. Prints 'spec|N'."""
import sys, math
lo, hi = int(sys.argv[1]), int(sys.argv[2])
out = []
for N in range(lo, hi + 1):
    for n in range(2, N + 1):
        if N % n: continue
        M = N // n
        for k in range(2, M + 1):
            if M % k: continue
            m = M // k
            if m < 3: continue
            seen = set()
            for r in range(2, m):
                if math.gcd(r, m) != 1 or pow(r, k, m) != 1: continue
                sub = frozenset(pow(r, j, m) for j in range(k))
                if sub in seen: continue
                seen.add(sub)
                out.append((N, 'meta %d %d %d %d' % (m, k, r, n)))
for N, s in sorted(out): print('%s|%d' % (s, N))
