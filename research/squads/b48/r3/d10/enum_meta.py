import math
def isprime(p):
    if p<2: return False
    i=2
    while i*i<=p:
        if p%i==0: return False
        i+=1
    return True
def order(r,m,cap=5000):
    if math.gcd(r,m)!=1: return None
    x=r%m; o=1
    while x!=1%m:
        x=x*r%m; o+=1
        if o>cap: return None
    return o
LO,HI=1243,1400
frob=[]
for N in range(LO,HI+1):
    for p in range(3,N+1):
        if N%p==0 and isprime(p):
            k=N//p
            if 3<=k<p and (p-1)%k==0:
                for r in range(2,p):
                    if order(r,p)==k:
                        frob.append((N,p,k,r)); break
print("FROB", len(frob))
for t in frob: print("F", *t)
comp=[]
for N in range(LO,HI+1):
    for m in range(4,N):
        if N%m: continue
        k=N//m
        if k<3 or isprime(m): continue
        for r in range(2,m):
            if math.gcd(r-1,m)!=1: continue
            if order(r,m)==k:
                comp.append((N,m,k,r)); break
print("COMP", len(comp))
for t in comp: print("C", *t)
