def isprime(n):
    if n<2: return False
    if n%2==0: return n==2
    i=3
    while i*i<=n:
        if n%i==0: return False
        i+=2
    return True
def rord(k,p):
    # element of order exactly k mod p, or None (k | p-1 assumed)
    for r in range(2,60):
        s=pow(r,(p-1)//k,p)
        ok=True
        for q in range(2,k+1):
            if k%q==0 and all(q%d for d in range(2,q)) and pow(s,k//q,p)==1: ok=False;break
        if ok and pow(s,k,p)==1 and s!=1: return s
    return None
out=[]
for k in range(3,64,2):
    for p in range(1+2*k,1100000//k+2,2*k):
        if p%k!=1 or not isprime(p) or p*k>1100000: continue
        if p*k<50: continue
        r=rord(k,p)
        if r: out.append((p,k,r,p*k))
F=out
res=[]
for a in F:
    for b in F:
        if (a[1],a[0])>(b[1],b[0]): continue
        N=a[3]*b[3]
        if 1056058<=N<=1065000 and max(a[1],b[1])>=17:
            res.append((N,a,b))
res.sort()
for N,a,b in res: print(N, "meta %d %d %d"%(a[0],a[1],a[2]), "meta %d %d %d"%(b[0],b[1],b[2]))
print(len(res), len(F))
