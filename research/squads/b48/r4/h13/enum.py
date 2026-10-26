# enumerate metacyclic Z_m x|_r Z_k, order N in [LO,HI], m odd (so gcd(r-1,m) odd), with no central involution:
# centre = {(a,j): r^j=1 mod m, (r-1)a=0 mod m} has order gcd(r-1,m)*(k/o); odd iff k/o odd (o=ord_m(r)).
import sys, math
LO, HI = int(sys.argv[1]), int(sys.argv[2])
def order_mod(r, m):
    x, o = r % m, 1
    while x != 1 % m:
        x = x * r % m; o += 1
    return o
seen = {}
out = []
for N in range(LO, HI + 1):
    for m in range(3, N + 1, 2):
        if N % m: continue
        k = N // m
        if k < 2: continue
        units_k = [t for t in range(1, k + 1) if math.gcd(t, k) == 1] if k > 1 else [1]
        for r in range(2, m):
            if math.gcd(r, m) != 1: continue
            if pow(r, k, m) != 1 % m: continue
            o = order_mod(r, m)
            if (k // o) % 2 == 0 and k % o == 0 and (k // o) % 2 == 1:
                pass
            if k % o: continue
            if (k // o) % 2 == 0: continue  # central involution exists
            # canonical rep under r -> r^t, gcd(t,k)=1
            canon = min(pow(r, t, m) for t in units_k)
            key = (N, m, k, canon)
            if canon != r: continue
            out.append((N, m, k, r, o, math.gcd(r - 1, m)))
for row in out:
    print(*row)
