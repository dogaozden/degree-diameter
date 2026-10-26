import math,sys
from math import gcd
# candidate metacyclic groups Z_m x|_r Z_k with k even (index-2 subgroup via j mod 2), order N=m*k
def order_mod(r,m):
    if m==1: return 1
    x=r%m; o=1
    while x!=1%m:
        x=x*r%m; o+=1
        if o>10000: return None
    return o
Ns=[int(a) for a in sys.argv[1].split(',')] if len(sys.argv)>1 else range(1094,1201,2)
out=[]
for N in Ns:
    for k in range(2,N+1,2):
        if N%k: continue
        m=N//k
        if m<3: continue
        units=[r for r in range(2,m) if gcd(r,m)==1]
        good=[]
        for r in units:
            if (pow(r,k,m))!=1%m: continue
            od=order_mod(r,m)
            if od and od>1: good.append((od,r))
        # keep one r per distinct order (smallest r)
        seen={}
        for od,r in good:
            seen.setdefault(od,r)
        for od,r in sorted(seen.items())[:2]:
            out.append((N,m,k,r,od))
for t in out: print("meta:%d:%d:%d N=%d order_r=%d"%(t[1],t[2],t[3],t[0],t[4]))
