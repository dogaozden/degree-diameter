from math import gcd
seen=[]
for N in range(1096,1105):
    for k in range(2,N):
        if N%k: continue
        m=N//k
        if m<2: continue
        for r in range(1,m):
            if gcd(r,m)!=1 or pow(r,k,m)!=1: continue
            # class rep: skip r if a smaller r' = r^j (gcd(j,k)=1) exists
            reps=set()
            for j in range(1,k+1):
                if gcd(j,k)==1: reps.add(pow(r,j,m))
            if r!=min(reps): continue
            seen.append((N,m,k,r))
for s in seen: print("N=%d meta:%d:%d:%d"%s)
