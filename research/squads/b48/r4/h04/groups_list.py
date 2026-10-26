import math
out=[]
for N in range(134,171):
    for k in range(2,N):
        if N%k: continue
        m=N//k
        if m<2: continue
        for r in range(1,m):
            if math.gcd(r,m)!=1: continue
            if pow(r,k,m)!=1%m: continue
            if r==1: continue  # abelian
            # order of r mod m must divide k (already), keep group nonabelian: r != 1 mod m
            # canonical-ish: skip r with r*r... keep all
            out.append((N,m,k,r))
print(len(out))
for x in out: print("meta:%d:%d:%d"%(x[1],x[2],x[3]), "N=",x[0], "m=",x[1],"k=",x[2],"r=",x[3])
