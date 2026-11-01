import sys
def isprime(n):
    if n<2: return False
    for q in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if n%q==0: return n==q
    d=n-1;s=0
    while d%2==0: d//=2;s+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        x=pow(a,d,n)
        if x in(1,n-1): continue
        for _ in range(s-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True
def pf(n):
    f=[];q=2
    while q*q<=n:
        if n%q==0:
            f.append(q)
            while n%q==0:n//=q
        q+=1
    if n>1:f.append(n)
    return f
res=[]
for k in range(29,64):
    lo=-(-22664905//k); hi=23200000//k
    for p in range(lo,hi+1):
        if (p-1)%k: continue
        if not isprime(p): continue
        g=None
        for a in range(2,200):
            r=pow(a,(p-1)//k,p)
            if r!=1 and all(pow(r,k//q,p)!=1 for q in pf(k)):
                g=r;break
        if g is None: continue
        res.append((p*k,p,k,g,(p-1)//k))
res.sort()
for t in res: print(*t)
print(len(res), file=sys.stderr)
