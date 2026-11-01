import math
def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
def order(r,p):
    x=r; k=1
    while x!=1:
        x=x*r%p; k+=1
    return k
def primroot(p):
    fac=[]; m=p-1; q=2
    while q*q<=m:
        if m%q==0:
            fac.append(q)
            while m%q==0: m//=q
        q+=1
    if m>1: fac.append(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//f,p)!=1 for f in fac): return g
res=[]
# N = p*k in [520885, 545000], p prime, k | p-1, 4<=k<200
for k in range(4,200):
    lo=-(-520885//k); hi=545000//k
    for p in range(lo,hi+1):
        if (p-1)%k: continue
        if not isprime(p): continue
        g=primroot(p); r=pow(g,(p-1)//k,p)
        assert order(r,p)==k
        divs=[d for d in range(2,64) if k%d==0]
        res.append((p*k,p,k,r,'fast' if (divs or k<=63) else 'slow'))
res.sort()
print(len(res))
for x in res: print(*x)
