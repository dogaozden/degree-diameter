import math, sys
def isprime(n):
    if n < 2: return False
    i = 2
    while i*i <= n:
        if n % i == 0: return False
        i += 1
    return True
def n_order(x, p):
    o = 1; y = x % p
    while y != 1:
        y = y*x % p; o += 1
    return o
W = 1 + sum(8*7**(2*i-1) for i in range(1,5))
lo, hi = int(sys.argv[1]), int(sys.argv[2])
out = []
for k in range(3, 400, 2):
    pmin = -(-lo // k); pmax = hi // k
    p = pmin
    while p <= pmax:
        if p > k and (p-1) % k == 0 and isprime(p):
            found = None
            for x in range(2, p):
                if pow(x, (p-1)//k, p) != 1: continue
                if n_order(x, p) == k:
                    found = x; break
            if found is not None:
                rset = [pow(found, j, p) for j in range(1, k) if math.gcd(j, k) == 1]
                N = p*k
                mu = N*math.exp(-W/N)
                out.append((N, p, k, min(rset), len(rset), round(mu,2)))
        p += k
out.sort()
for row in out[:60]:
    print("N=%d p=%d k=%d r_min=%d (#r=%d) mu=%.2f" % row)
print("W=", W, "count", len(out))
