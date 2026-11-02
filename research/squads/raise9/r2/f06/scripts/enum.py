import math, sys
def isprime(n):
    if n < 2: return False
    i = 2
    while i*i <= n:
        if n % i == 0: return False
        i += 1
    return True
def primes_of(k):
    s=set(); d=2
    while d*d<=k:
        while k%d==0: s.add(d); k//=d
        d+=1
    if k>1: s.add(k)
    return s
W = 1 + sum(8*7**(2*i-1) for i in range(1,5))
lo, hi = int(sys.argv[1]), int(sys.argv[2])
out = []
for k in range(3, 400, 2):
    pr = primes_of(k)
    pmin = -(-lo // k); pmax = hi // k
    p = pmin + ((1 - pmin) % k)
    while p <= pmax:
        if p > k and (p-1) % k == 0 and isprime(p):
            e = (p-1)//k
            found = None
            for x in range(2, 200):
                h = pow(x, e, p)
                if h == 1: continue
                if all(pow(h, k//q, p) != 1 for q in pr):
                    found = h; break
            if found is not None:
                rset = [pow(found, j, p) for j in range(1, k) if math.gcd(j, k) == 1]
                N = p*k
                mu = N*math.exp(-W/N)
                out.append((N, p, k, min(rset), len(rset), round(mu,2)))
        p += k
out.sort()
with open("cands.tsv","w") as f:
    for row in out: f.write("%d\t%d\t%d\t%d\t%.2f\n" % (row[1],row[2],row[3],row[0],row[5]))
for row in out[:0]:
    print("N=%d p=%d k=%d r_min=%d (#r=%d) mu=%.2f" % row)
print("W=", W, "count", len(out))
