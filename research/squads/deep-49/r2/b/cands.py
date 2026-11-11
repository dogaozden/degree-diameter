import sys
from math import gcd
def ncinv(m,k,r):
    # elements (a,j) of Z_m x|_r Z_k; (a,j)(b,l) = (a + r^j b, j+l)
    rp=[pow(r,j,m) for j in range(k)]
    c=0
    for j in range(k):
        if (2*j)%k: continue
        for a in range(m):
            if (a + rp[j]*a) % m: continue
            if j==0 and a==0: continue
            central = (rp[j]==1%m) and (a*(r-1))%m==0
            if not central: c+=1
    return c
def orbit_min(m,k,r):
    best=r
    for t in range(1,k):
        if gcd(t,k)==1:
            best=min(best,pow(r,t,m))
    return best
def enum(lo,hi,mode):
    out=[]
    for N in range(lo,hi+1):
        if mode=='hub' and N%4: continue
        for m in range(3,N):
            if N%m: continue
            k=N//m
            if k<2: continue
            if mode=='mix' and k%2: continue
            seen=set()
            for r in range(2,m):
                if gcd(r,m)!=1 or pow(r,k,m)!=1%m: continue
                if mode=='mix' and pow(r,k//2,m)==1%m: continue
                if mode=='hub':
                    gg=k*gcd(r-1,m)
                    if gg>309: continue
                d=1; x=r
                while x!=1%m: x=x*r%m; d+=1
                rep=orbit_min(m,k,r)
                if rep in seen: continue
                seen.add(rep)
                if mode=='mix':
                    c=ncinv(m,k,rep)
                    if c<10: continue
                    out.append((d,N,m,k,rep,c))
                else:
                    out.append((d,N,m,k,rep,k*gcd(rep-1,m)))
    return out
mode=sys.argv[1]
if mode=='mix':
    res=enum(2486,2600,'mix')
    res.sort(key=lambda t:(-t[0],-t[1]))
    print("count",len(res))
    for t in res[:40]: print("d=%d N=%d m=%d k=%d r=%d ninv=%d"%(t[0],t[1],t[2],t[3],t[4],t[5]))
else:
    res=enum(1992,2100,'hub')
    res.sort(key=lambda t:(-t[0],-t[1]))
    print("count",len(res))
    for t in res[:40]: print("d=%d N=%d m=%d k=%d r=%d G/G'=%d"%(t[0],t[1],t[2],t[3],t[4],t[5]))
