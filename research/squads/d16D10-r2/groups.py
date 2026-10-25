import math, sys
W = 16*sum(15**(2*i) for i in range(5))
def isprime(x):
    if x < 2: return False
    i = 2
    while i*i <= x:
        if x % i == 0: return False
        i += 1
    return True
def factor(n):
    f = {}; d = 2
    while d*d <= n:
        while n % d == 0: f[d] = f.get(d,0)+1; n //= d
        d += 1
    if n > 1: f[n] = f.get(n,0)+1
    return f
def bestfix(n, k):
    # min over r with r^k = 1 mod n, r != 1 of gcd(r-1, n)
    if n == 1: return 1
    return 1 if all((q-1) % k == 0 for q in factor(n)) else n
lo, hi = float(sys.argv[1]), float(sys.argv[2]); k = int(sys.argv[3])
rows = []
for p in range(5, 2000):
    if not isprime(p): continue
    if (p-1) % k == 0: tor = p-1
    elif (p+1) % k == 0: tor = p+1
    else: continue
    for fam in ('sl', 'psl'):
        o = p*(p*p-1) // (2 if fam == 'psl' else 1)
        t = tor if fam == 'sl' else tor//2
        for n in range(max(1, int(lo/o)), int(hi/o)+2):
            N = o*n
            if N < lo or N > hi or math.gcd(n, p) != 1: continue
            fz = bestfix(n, k)
            if fz > 1 and n > 1: continue
            lam = W/N; mu = N*math.exp(-lam)
            fixh = t*fz*math.exp(-lam/k)
            H = mu/k + fixh
            rows.append((N, fam, p, n, mu, mu/k, t*fz, fixh, H, p*n))
rows.sort()
for r in rows: print("%d %s %d n=%d mu=%.1f mu/k=%.1f fix=%d fixholes=%.2f H=%.1f rowlen=%d" % r)
