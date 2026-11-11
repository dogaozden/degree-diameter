import sys
from math import gcd
def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
def order(r,p):
    x=1;o=0
    while True:
        x=x*r%p;o+=1
        if x==1: return o
def frob_list(Nlo,Nhi,kmin,kmax):
    out=[]
    for p in range(3,Nhi):
        if not isprime(p): continue
        for k in range(kmin,kmax+1):
            if (p-1)%k: continue
            N=p*k
            if N<Nlo or N>Nhi: continue
            # find r with order exactly k
            rs=[r for r in range(2,p) if order(r,p)==k][:1] if k>1 else []
            if rs: out.append((N,p,k,rs[0]))
    return out
mode=sys.argv[1]
if mode=='single':
    L=frob_list(1149121,1165000,13,63)
    L.sort()
    for N,p,k,r in L: print(N,p,k,r)
    print("count",len(L))
elif mode=='a4':
    L=frob_list(95760,97083,3,63)
    for N,p,k,r in sorted(L): print(N,p,k,r)
    print("count",len(L))
elif mode=='z7':
    L=frob_list(54720,55480,3,63)
    for N,p,k,r in sorted(L): print(N,p,k,r)
    print("count",len(L))
