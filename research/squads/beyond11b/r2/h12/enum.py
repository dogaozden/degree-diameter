import sys
lo,hi=int(sys.argv[1]),int(sys.argv[2])
def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
def factors(n):
    f=set(); i=2
    while i*i<=n:
        while n%i==0: f.add(i); n//=i
        i+=1
    if n>1: f.add(n)
    return f
def pw(a,e,m): return pow(a,e,m)
def primroot(p):
    fs=factors(p-1)
    for g in range(2,p):
        if all(pw(g,(p-1)//q,p)!=1 for q in fs): return g
out=[]
for p in range(3,hi//2+1):
    if not isprime(p): continue
    g=primroot(p)
    for k in range(2,p):
        if (p-1)%k or p*k>hi: continue
        if p*k*1<lo and p*k*1*1>hi: continue
        r=pw(g,(p-1)//k,p)
        n=1
        while p*k*n<=hi:
            N=p*k*n
            if lo<=N: out.append((N,p,k,r,n))
            n+=1
for x in sorted(out): print(*x)
