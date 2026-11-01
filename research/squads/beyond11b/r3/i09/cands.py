# list (k, p, r) with p prime, k | p-1, p*k in (5506488, 5600000], r of exact order k mod p
import sys
def isprime(n):
    if n < 2: return False
    for q in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if n % q == 0: return n == q
    d, s = n-1, 0
    while d % 2 == 0: d//=2; s+=1
    for a in [2,3,5,7,11,13,17]:
        x = pow(a, d, n)
        if x in (1, n-1): continue
        for _ in range(s-1):
            x = x*x % n
            if x == n-1: break
        else: return False
    return True
def factors(n):
    f=[]; d=2
    while d*d<=n:
        if n%d==0:
            f.append(d)
            while n%d==0: n//=d
        d+=1
    if n>1: f.append(n)
    return f
def order(r,p,k):
    # exact order of r mod p, assumed to divide k
    o=k
    for q in factors(k):
        while o%q==0 and pow(r,o//q,p)==1: o//=q
    return o
ks=[int(x) for x in sys.argv[1:]] or [29,31,37,41,43,47,53,59,61,63]
lo,hi=5506488,5600000
for k in ks:
    out=[]
    pmin=lo//k+1; pmax=hi//k
    for p in range(pmin,pmax+1):
        if (p-1)%k or not isprime(p): continue
        # find r of exact order k
        for g in range(2,200):
            r=pow(g,(p-1)//k,p)
            if r!=1 and order(r,p,k)==k:
                out.append((p,r)); break
        if len(out)>=6: break
    print(k, [(p,r,p*k) for p,r in out])
