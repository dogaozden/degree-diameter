import math
def cands(lo, hi, kmin=12):
    out=[]
    for k in range(kmin, hi+1):
        for m in range(2, hi//k+2):
            N=m*k
            if N<lo or N>hi: continue
            for r in range(2, m):
                if math.gcd(r,m)!=1: continue
                if pow(r,k,m)!=1: continue
                # order of r mod m
                o=1; x=r%m
                while x!=1: x=x*r%m; o+=1
                if o==1: continue
                out.append((N,m,k,r,o))
    return out
import sys
lo,hi=int(sys.argv[1]),int(sys.argv[2])
for c in cands(lo,hi): print(*c)
