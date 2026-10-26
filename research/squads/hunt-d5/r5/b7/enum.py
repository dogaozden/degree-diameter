def isprime(n):
    return n>1 and all(n%q for q in range(2,int(n**0.5)+1))
def divisors(n):
    return [d for d in range(1,n+1) if n%d==0]
def primfactors(n):
    f=set();q=2
    while q*q<=n:
        while n%q==0: f.add(q); n//=q
        q+=1
    if n>1: f.add(n)
    return f
out=[]
for n in (2,3):
    for p in range(3,2000):
        if not isprime(p): continue
        for k in divisors(p-1):
            if k<3: continue
            N=p*k*n
            if not (606<=N<=660): continue
            g=next(a for a in range(2,p) if all(pow(a,(p-1)//q,p)!=1 for q in primfactors(p-1)))
            for e in divisors(k):
                if e<2: continue
                r=pow(g,(p-1)//e,p)
                out.append((N,p,k,r,n,e))
for N,p,k,r,n,e in sorted(out):
    print(N,"meta",p,k,r,n,"act_order",e, "faithful" if e==k else "")
print(len(out))
