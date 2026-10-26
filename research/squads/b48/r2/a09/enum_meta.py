# enumerate metacyclic Z_m x|_r Z_k with order m*k in [LO,HI], ord(r) = t >= 6 (t divides k), r unit mod m
import sys, math
LO, HI = int(sys.argv[1]), int(sys.argv[2])
for N in range(LO, HI + 1):
    for k in range(2, N + 1):
        if N % k: continue
        m = N // k
        if m < 2: continue
        for r in range(2, m):
            if math.gcd(r, m) != 1: continue
            o, x = 1, r % m
            while x != 1:
                x = x * r % m; o += 1
                if o > k: break
            if o > k or k % o: continue
            if o < 6: continue
            print(N, m, k, r, o)
