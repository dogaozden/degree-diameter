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
out=[]
for p in range(3,2801):
    if not isprime(p): continue
    for k in range(8,p):
        if (p-1)%k: continue
        if p*k<2200 or p*k>2800: continue
        r=next(r for r in range(2,p) if order(r,p)==k)
        out.append((p*k,p,k,r))
out.sort()
for N,p,k,r in out: print(N,p,k,r)
print("count",len(out))
