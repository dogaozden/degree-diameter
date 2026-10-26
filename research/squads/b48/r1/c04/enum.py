from math import gcd
import sys
ks=[8,16,32,9,18,27,36]
out=[]
for k in ks:
    for m in range(1094//k, 1200//k+2):
        N=m*k
        if N<1094 or N>1200: continue
        seen=set()
        for r in range(1,m):
            if gcd(r,m)!=1: continue
            if pow(r,k,m)!=1: continue
            # class under r->r^j, gcd(j,k)=1
            cl=min(pow(r,j,m) for j in range(1,k+1) if gcd(j,k)==1)
            if cl in seen: continue
            seen.add(cl)
            # order of r
            d=1; x=r
            while x!=1: x=x*r%m; d+=1
            out.append((N,m,k,cl,d))
out.sort()
for o in out: print(*o)
print(len(out), file=sys.stderr)
