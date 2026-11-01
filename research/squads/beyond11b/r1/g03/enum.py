import math
from math import gcd
res=[]
for N in range(148825,170001):
    for k in range(9,200,2):
        if N%k: continue
        m=N//k
        if m%2==0: continue
        if m<2: continue
        # r in (Z/m)^*, r^k=1 mod m, order of r divides k
        # quick: nonabelian r !=1
        if m>2000000: continue
        cnt=0
        # enumerate r candidates only if m small-ish
        ok=[]
        for r in range(2,m):
            if gcd(r,m)!=1: continue
            if pow(r,k,m)==1 and r!=1:
                ok.append(r)
                if len(ok)>=3: break
        if ok:
            res.append((N,m,k,ok))
print(len(res))
for x in res[:60]: print(x)
