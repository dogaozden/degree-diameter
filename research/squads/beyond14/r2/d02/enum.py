import sys
from math import gcd
def order(r,m):
    x=r%m; d=1
    while x!=1%m: x=x*r%m; d+=1
    return d
out=[]
for N in range(792,1001):
    for k in range(3,N):
        if N%k: continue
        m=N//k
        if m<3: continue
        for r in range(2,m):
            if gcd(r,m)!=1: continue
            d=order(r,m)
            if k%d or d<2 or d>=k: continue
            if pow(r,k,m)!=1%m: continue
            # prefer non-faithful with central b^d; record
            out.append((N,m,k,r,d))
# keep one r per (m,k,d) class up to powers: report all count
import collections
print(len(out))
# list distinct (m,k,d) with a representative r of order d
seen={}
for N,m,k,r,d in out:
    key=(m,k,d)
    if key not in seen: seen[key]=(N,r)
for (m,k,d),(N,r) in sorted(seen.items(), key=lambda t:(t[1][0],t[0])):
    print(N,m,k,r,d)
