import math,sys
lo,hi=int(sys.argv[1]),int(sys.argv[2])
out=[]
for N in range(lo,hi+1):
    for k in range(2,N):
        if N%k: continue
        m=N//k
        if m<3: continue
        for r in range(2,m):
            if math.gcd(r,m)!=1: continue
            if pow(r,k,m)!=1: continue
            # order of r
            o=1; x=r
            while x!=1: x=x*r%m; o+=1
            if o<3: continue
            out.append((N,m,k,r,o))
for t in out: print(*t)
print("count",len(out),file=sys.stderr)
