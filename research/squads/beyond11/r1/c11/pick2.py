import math, sys
def isprime(x):
    if x < 2: return False
    i = 2
    while i * i <= x:
        if x % i == 0: return False
        i += 1
    return True
d, D = int(sys.argv[1]), int(sys.argv[2]); mlo, mhi = float(sys.argv[3]), float(sys.argv[4])
if D % 2 == 0: W = sum(d*(d-1)**(2*i) for i in range(D//2))
else: W = 1 + sum(d*(d-1)**(2*i-1) for i in range(1,(D-1)//2+1))
mu = lambda N: N*math.exp(-W/N)
def bisect_N(target):
    lo, hi = 1e6, 1e12
    for _ in range(200):
        m = (lo+hi)/2
        if mu(m) < target: lo = m
        else: hi = m
    return lo
Nlo, Nhi = bisect_N(mlo), bisect_N(mhi)
out = []
for p in range(5, 4000):
    if not isprime(p): continue
    for fam, base in (("sl", p*(p*p-1)), ("psl", p*(p*p-1)//2)):
        for n in range(1, int(Nhi/base)+2):
            if n*base < Nlo: continue
            if n*base > Nhi: break
            if n > 1 and not (n % 3 == 1 and isprime(n)): continue
            if math.gcd(p, n) != 1: continue
            out.append((fam, p, n, n*base, mu(n*base)))
for fam, p, n, N, m in sorted(out, key=lambda x: x[3]):
    print("%s p=%d n=%d N=%d mu=%.3f n/p=%.3f" % (fam, p, n, N, m, n/p))
