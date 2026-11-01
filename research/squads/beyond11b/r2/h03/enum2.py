def isprime(x):
    if x<2: return False
    i=2
    while i*i<=x:
        if x%i==0: return False
        i+=1
    return True
F=[]
for p in range(3,400):
    if not isprime(p): continue
    for k in range(3,p,2):
        if (p-1)%k==0:
            r=next(r for r in range(2,p) if pow(r,k,p)==1 and r!=1)
            F.append((p*k,p,k,r))
F.sort()
small=[f for f in F if f[0]<=100]
big=F
res=[]
for a in small:
    for b in big:
        N=a[0]*b[0]
        if 14470<=N<=15300 and a[0]<=b[0]:
            res.append((N,a,b))
for N,a,b in sorted(res)[:40]:
    print(N,"meta",a[1],a[2],a[3],"x meta",b[1],b[2],b[3],"orders",a[0],b[0])
