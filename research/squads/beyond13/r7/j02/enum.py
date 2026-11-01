import math,sys
lo,hi=14879,15500
def isprime(x):
    if x<2: return False
    i=2
    while i*i<=x:
        if x%i==0: return False
        i+=1
    return True
out=[]
for N in range(lo,hi+1):
    if N%2==0: continue
    for k in range(13,N+1,2):
        if N%k: continue
        m=N//k
        if m%2==0 or m<3: continue
        if k>m: continue
        # find r units mod m with r^k=1 mod m, r!=1, order of r divides k
        cands=[]
        for r in range(2,m):
            if math.gcd(r,m)!=1: continue
            if pow(r,k,m)==1:
                cands.append(r)
                if len(cands)>=3: break
        if cands:
            out.append((N,m,k,cands[:3],isprime(m)))
for o in out: print(o)
print(len(out))
