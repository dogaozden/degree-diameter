import math
rows = []
for N in range(2486, 2601):
    for k in range(2, N):
        if N % k: continue
        m = N // k
        if m < 3: continue
        for r in range(2, m):
            if math.gcd(r, m) != 1 or pow(r, k, m) != 1 % m: continue
            inv = 0
            for j in range(k):
                if (2*j) % k == 0 and j != 0:
                    inv += math.gcd((1 + pow(r, j, m)) % m, m)
            if N % 2 == 0 and inv == 0: inv = -1  # should not happen
            rows.append((N, m, k, r, inv, math.gcd(r-1, m)))
# many: even k, m odd, r^(k/2) = -1 mod m (inv = m); also even-order with largest inv
many = [x for x in rows if x[2] % 2 == 0 and x[1] % 2 == 1 and pow(x[3], x[2]//2, x[1]) == x[1]-1 and x[5] == 1]
print("many-inv (m odd, k even, r^(k/2)=-1, gcd(r-1,m)=1):", len(many))
for x in many[:12]: print("MANY N=%d m=%d k=%d r=%d inv=%d g=%d" % x)
few = sorted([x for x in rows if x[4] >= 1 and x[5] == 1], key=lambda x: (x[4], -x[0]))
print("few-inv with gcd(r-1,m)=1 (sorted by inv):", len(few))
for x in few[:25]: print("FEW N=%d m=%d k=%d r=%d inv=%d g=%d" % x)
odd = [x for x in rows if x[4] == 0 and x[5] == 1]
print("odd with gcd 1:", len(odd))
for x in odd[:10]: print("ODD N=%d m=%d k=%d r=%d inv=%d g=%d" % x)
