from math import gcd
LO, HI = 262081, 265000
def isprime(n):
    if n < 2: return False
    i = 2
    while i*i <= n:
        if n % i == 0: return False
        i += 1
    return True
def factor(n):
    f = []; d = 2
    while d*d <= n:
        while n % d == 0: f.append(d); n //= d
        d += 1
    if n > 1: f.append(n)
    return f
def primroot(p):
    fs = set(factor(p-1))
    for g in range(2, p):
        if all(pow(g, (p-1)//q, p) != 1 for q in fs): return g
frob = []
for p in range(3, HI):
    if not isprime(p): continue
    for k in range(3, p, 2):
        if (p-1) % k: continue
        N1 = p*k
        if N1 > HI: break
        g = primroot(p)
        r = pow(g, (p-1)//k, p)
        frob.append((N1, p, k, r))
frob.sort()
res = []
for i,(a,p1,k1,r1) in enumerate(frob):
    for (b,p2,k2,r2) in frob[i:]:
        N = a*b
        if N > HI: break
        if N >= LO:
            res.append((N, p1,k1,r1, p2,k2,r2, gcd(a,b)))
res.sort()
print(len(res))
for x in res[:60]: print(x)
