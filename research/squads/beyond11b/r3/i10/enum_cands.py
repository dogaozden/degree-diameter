def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
def order(r,p):
    x=r; o=1
    while x!=1:
        x=x*r%p; o+=1
    return o
res=[]
for k in range(20,64):
    for p in range(2,40000):
        N=p*k
        if N<34454 or N>38000: continue
        if not isprime(p): continue
        if (p-1)%k: continue
        rs=[r for r in range(2,p) if order(r,p)==k]
        res.append((N,k,p,rs[0],len(rs)))
for x in sorted(res): print(*x)
