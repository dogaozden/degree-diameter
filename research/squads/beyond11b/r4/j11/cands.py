import sys
lo,hi=4683121,4750000
def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
def primroot(p):
    fac=[];n=p-1;d=2
    while d*d<=n:
        if n%d==0:
            fac.append(d)
            while n%d==0: n//=d
        d+=1
    if n>1: fac.append(n)
    for g in range(2,p):
        if all(pow(g,(p-1)//f,p)!=1 for f in fac): return g
out=[]
for k in range(40,64):
    for p in range(lo//k, hi//k+2):
        N=p*k
        if lo<=N<=hi and (p-1)%k==0 and isprime(p):
            g=primroot(p); r=pow(g,(p-1)//k,p)
            assert pow(r,k,p)==1 and all(pow(r,j,p)!=1 for j in range(1,k) if k%j==0)
            out.append((N,k,p,r))
for N,k,p,r in sorted(out): print(N,k,p,r)
