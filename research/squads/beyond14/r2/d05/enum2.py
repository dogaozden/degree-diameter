from math import gcd
def isprime(n): return n>1 and all(n%q for q in range(2,int(n**.5)+1))
res=[]
for N in range(2150,2401):
    for k in range(2,N):
        if N%k: continue
        m=N//k
        if m<3: continue
        for r in range(2,m):
            if gcd(r,m)!=1 or pow(r,k,m)!=1: continue
            if not isprime(m): continue
            if all((pow(r,j,m)-1)%m for j in range(1,k)):
                if r==min(pow(r,j,m) for j in range(1,k)) or True:
                    res.append((N,m,k,r))
            break_ = None
# keep one r per (m,k) subgroup: smallest r
seen=set(); out=[]
for N,m,k,r in res:
    key=(m,k,frozenset(pow(r,j,m) for j in range(k)))
    if key in seen: continue
    seen.add(key); out.append((N,m,k,r))
for x in out: print(x)
