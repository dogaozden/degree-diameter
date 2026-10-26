# enumerate metacyclic Z_m x|_r Z_p, p prime >= 5, N = m*p in [1094,1250]
# classes: cyclic subgroups of order p in Z_m^* (r ~ r^j gives isomorphic groups)
from math import gcd
def isprime(n):
    return n>1 and all(n%d for d in range(2,int(n**0.5)+1))
out=[]
for p in [5,7,11,13,17,19,23,29,31,37]:
    for N in range(1094,1251):
        if N%p: continue
        m=N//p
        if m<2: continue
        seen=set()
        for r in range(2,m):
            if gcd(r,m)!=1: continue
            if pow(r,p,m)!=1: continue
            # order exactly p
            if r==1: continue
            sub=frozenset(pow(r,i,m) for i in range(p))
            if len(sub)!=p: continue
            if sub in seen: continue
            seen.add(sub)
            out.append((N,m,p,r))
        # abelian control (r=1): cyc only if gcd(m,p)=1; skip (abelian stalls)
for row in out: print(*row)
import sys
print("count",len(out),file=sys.stderr)
