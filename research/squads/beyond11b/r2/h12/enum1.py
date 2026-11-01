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
def primroot(p):
    fs=factors(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g
for k in range(2,hi):
    for p in range(lo//k, hi//k+1):
        if p<3 or (p-1)%k or p*k<lo or p*k>hi or not isprime(p): continue
        g=primroot(p); r=pow(g,(p-1)//k,p)
        print(p*k,p,k,r)
