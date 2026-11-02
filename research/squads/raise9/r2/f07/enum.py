import math,sys
W=19173961
def isprime(x):
    if x<2: return False
    i=2
    while i*i<=x:
        if x%i==0: return False
        i+=1
    return True
out=[]
for k in range(13,64,2):
    # primes p with p = 1 mod k, N = p*k in range
    lo=1749889; hi=2000000
    for p in range(lo//k, hi//k+2):
        if p%k!=1 or not isprime(p): continue
        N=p*k
        if N<lo or N>hi: continue
        # elements of order k mod p
        ords=[]
        g=None
        # find r of order exactly k
        rs=[]
        for r in range(2,min(p,200000)):
            if pow(r,k,p)==1 and all(pow(r,k//q,p)!=1 for q in range(2,k+1) if k%q==0 and isprime(q)):
                rs.append(r)
                if len(rs)>=3: break
        if not rs: continue
        mu=N*math.exp(-W/N)
        out.append((N,p,k,rs,round(mu,2)))
out.sort()
for o in out: print("N=%d p=%d k=%d r=%s mu=%s"%o)
print(len(out))
