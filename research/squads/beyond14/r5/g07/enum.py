import math
def ordmod(r,m):
    x=r%m; k=1
    while x!=1%m: x=x*r%m; k+=1
    return k
def cands(lo,hi,kmin):
    out=[]
    for N in range(lo,hi+1):
        for k in range(kmin,N+1):
            if N%k: continue
            m=N//k
            if m<2: continue
            for r in range(2,m):
                if math.gcd(r,m)!=1: continue
                if pow(r,k,m)!=1: continue
                o=ordmod(r,m)
                if o<2: continue
                out.append((N,m,k,r,o))
    return out
import sys
lo,hi,kmin=map(int,sys.argv[1:4])
for N,m,k,r,o in cands(lo,hi,kmin):
    print(N,f"meta:{m}:{k}:{r}",f"ord_r={o}", "faithful" if o==k else "")
