import math,sys
lo,hi=int(sys.argv[1]),int(sys.argv[2])
res=[]
for k in range(12, hi+1):
    for m in range(2, hi//k+2):
        N=m*k
        if N<lo or N>hi: continue
        for r in range(2, m):
            if math.gcd(r,m)!=1 or math.gcd(r-1,m)!=1: continue
            if pow(r,k,m)!=1: continue
            o=1; x=r
            while x!=1: x=x*r%m; o+=1
            if o!=k: continue
            res.append((N,m,k,r))
print(len(res))
import collections
by=collections.Counter(c[2] for c in res)
print(sorted(by.items()))
for c in res:
    if c[2] in (12,13,14,15,16,18,20,21,24,26,28,30): print(*c)
