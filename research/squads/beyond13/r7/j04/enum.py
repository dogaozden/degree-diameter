import math,sys
lo,hi=int(sys.argv[1]),int(sys.argv[2])
out=[]
for k in range(3,400):
    for m in range(3,hi//k+1):
        N=m*k
        if N<lo or N>hi: continue
        if math.gcd(m,k)!=1 and False: pass
        # need r with r^k=1 mod m, gcd(r,m)=1, r != 1 (nontrivial action), r order divides k
        seen=set()
        for r in range(2,m):
            if math.gcd(r,m)!=1: continue
            if pow(r,k,m)!=1: continue
            # order of r
            o=1; x=r
            while x!=1: x=x*r%m; o+=1
            if o==1: continue
            if (m,r%m) in seen: continue
            out.append((N,m,k,r,o))
            break
out.sort()
for t in out: print(*t)
print(len(out),file=sys.stderr)
