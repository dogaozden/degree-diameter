# Enumerate metacyclic groups meta m k r = Z_m x|_r Z_k with r^k = 1 mod m, r unit,
# classes under r -> r^j (gcd(j,k)=1). Targets: k=20 (m=55..62), k=10 (m=110..124), k=40 (m=28..31).
from math import gcd
def classes(m,k):
    units=[r for r in range(2,m) if gcd(r,m)==1 and pow(r,k,m)==1]
    js=[j for j in range(1,k) if gcd(j,k)==1]
    seen=set(); out=[]
    for r in units:
        if r in seen: continue
        orb={pow(r,j,m) for j in js}
        seen|=orb
        out.append(r)
    return out
def order(r,m):
    o=1; x=r
    while x!=1: x=x*r%m; o+=1
    return o
res=[]
for k,ms in [(20,range(55,63)),(10,range(110,125)),(40,range(28,32))]:
    for m in ms:
        N=m*k
        if not (1094<=N<=1240): continue
        for r in classes(m,k):
            res.append((N,m,k,r,order(r,m)))
for t in res: print(*t)
print("total",len(res),file=__import__('sys').stderr)
