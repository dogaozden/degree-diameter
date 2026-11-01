def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
def order(r,p):
    x=r%p; k=1
    while x!=1:
        x=x*r%p; k+=1
    return k
def frob(maxN):
    out=[]
    for k in range(3,64,2):
        for p in range(5, maxN//k+2, 2):
            if p*k>maxN: break
            if (p-1)%k or not isprime(p): continue
            N=p*k
            rs=[r for r in range(2,p) if order(r,p)==k]
            if rs: out.append((p,k,min(rs),N))
    return out
F=[f for f in frob(1100000) if f[3]>=50]
res=[]
for a in F:
    for b in F:
        if (a[1],a[0])>(b[1],b[0]): continue
        N=a[3]*b[3]
        if 1056058<=N<=1065000 and max(a[1],b[1])>=17:
            res.append((N,a,b))
res.sort()
for N,a,b in res: print(N, "meta %d %d %d"%(a[0],a[1],a[2]), "meta %d %d %d"%(b[0],b[1],b[2]))
print(len(res))
