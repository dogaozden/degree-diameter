import math,sys
lo,hi,kmin=int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3])
W=1+4*sum(3**(2*i-1) for i in range(1,5))
rows=[]
for k in range(kmin,hi,2):
    for m in range(3,hi//k+1,2):
        N=m*k
        if N<lo or N>hi or math.gcd(m,k)!=1: continue
        rs=[]
        for r in range(2,m):
            if math.gcd(r,m)!=1 or pow(r,k,m)!=1: continue
            o=1;x=r
            while x!=1: x=x*r%m;o+=1
            if o>1: rs.append((o,r))
        # group by order of r
        byo={}
        for o,r in rs: byo.setdefault(o,r)
        for o,r in byo.items():
            rows.append((N,m,k,r,o,round(N*math.exp(-W/N),2)))
rows.sort()
for t in rows[:60]: print(*t)
print(len(rows),file=sys.stderr)
