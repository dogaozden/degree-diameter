import math
from cands import out
def has3(n):
    best=None
    for r in range(2,n):
        if math.gcd(r,n)!=1: continue
        if pow(r,3,n)==1 and r!=1:
            fix=sum(1 for z in range(n) if (r*z-z)%n==0)
            if best is None or fix<best[1]: best=(r,fix)
    return best
for kind,p,n,N in out:
    b=has3(n)
    if b: print(kind,p,n,N,"r=",b[0],"fixed_z=",b[1])
