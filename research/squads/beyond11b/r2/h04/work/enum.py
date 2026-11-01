import math
LO,HI=150601,158000
def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
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
def ordr(r,p):
    x=r;o=1
    while x!=1: x=x*r%p;o+=1
    return o
rows=[]
for k in range(9,151,2):
    for p in range(LO//k, HI//k+2):
        N=p*k
        if LO<=N<=HI and p>k and isprime(p) and (p-1)%k==0:
            g=primroot(p); r=pow(g,(p-1)//k,p)
            assert ordr(r,p)==k
            rows.append((k,p,N,r))
print(len(rows))
for t in rows: print(*t)
