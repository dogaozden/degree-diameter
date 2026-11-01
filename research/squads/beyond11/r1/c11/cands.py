import math, sys
def isprime(x):
    if x < 2: return False
    i = 2
    while i * i <= x:
        if x % i == 0: return False
        i += 1
    return True
d, D, k = int(sys.argv[1]), int(sys.argv[2]), 3
target = float(sys.argv[3])
if D % 2 == 0: W = sum(d*(d-1)**(2*i) for i in range(D//2))
else: W = 1 + sum(d*(d-1)**(2*i-1) for i in range(1,(D-1)//2+1))
primes = [p for p in range(5, 400) if isprime(p)]
ns = [1] + [q for q in range(2, 200000) if isprime(q) and q % k == 1]
res = []
for p in primes:
    for fam, base in (("sl", p*(p*p-1)), ("psl", p*(p*p-1)//2)):
        # pick n near target size: N=base*n with mu near target
        for n in ns:
            if math.gcd(p, n) != 1: continue
            N = base*n
            if N > 1e9: break
            mu = N*math.exp(-W/N)
            if abs(mu-target)/target < 0.05 and (n==1 or True):
                res.append((fam, p, n, N, mu, n/p))
for r in sorted(res, key=lambda r: r[3]):
    print("%s p=%d n=%d N=%d mu=%.2f n/p=%.2f" % (r[0], r[1], r[2], r[3], r[4], r[5]))
