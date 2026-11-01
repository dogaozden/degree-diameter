import sys
lo,hi=int(sys.argv[1]),int(sys.argv[2])
def isprime(n):
    return n>1 and all(n%q for q in range(2,int(n**0.5)+1))
def order(r,p):
    x=r%p; k=1
    while x!=1: x=x*r%p; k+=1
    return k
out=[]
for p in range(3,hi+1):
    if not isprime(p): continue
    for k in range(2,p):
        if (p-1)%k: continue
        if p*k>hi: break
        rs=[r for r in range(2,p) if order(r,p)==k]
        if not rs: continue
        r=min(rs)
        n=1
        while p*k*n<=hi:
            N=p*k*n
            if lo<=N: out.append((N,p,k,r,n))
            n+=1
for x in sorted(out): print(*x)
