import math, sys
from collections import defaultdict
def classes(m,k):
    units=[r for r in range(1,m) if math.gcd(r,m)==1 and pow(r,k,m)==1 and r!=1 % m]
    seen=set(); reps=[]
    for r in units:
        if r in seen: continue
        orb=set()
        for j in range(1,k+1):
            if math.gcd(j,k)==1:
                orb.add(pow(r,j,m))
        seen|=orb
        reps.append((r,min(orb)))
    return reps
out=[]
for N in range(1094,1201):
    for k in (6,12,24):
        if N%k: continue
        m=N//k
        if m<2: continue
        for r,_ in classes(m,k):
            out.append((N,m,k,r))
print(len(out))
import collections
c=collections.Counter((k) for _,_,k,_ in out); print(c)
for x in out[:400]: print(*x)
