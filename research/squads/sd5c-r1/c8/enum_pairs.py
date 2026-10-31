import math
facs=[]
for m in range(2,160):
    for k in range(2,160):
        if m*k>150: break
        for r in range(2,m):
            if math.gcd(r,m)!=1 or pow(r,k,m)!=1: continue
            facs.append((m*k,m,k,r))
facs=sorted(set(facs))
out=[]
for (o1,m1,k1,r1) in facs:
    for (o2,m2,k2,r2) in facs:
        if (m1,k1,r1)>(m2,k2,r2): continue
        N=o1*o2
        if 5851<=N<=6000:
            out.append((N,(m1,k1,r1),(m2,k2,r2)))
out.sort()
print(len(out))
for x in out[:60]: print(x)
