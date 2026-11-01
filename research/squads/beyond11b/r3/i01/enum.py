def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
def factor(n):
    f=[];i=2
    while i*i<=n:
        while n%i==0: f.append(i); n//=i
        i+=1
    if n>1: f.append(n)
    return set(f)
def primroot(p):
    fs=factor(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g
out=[]
for k in (29,31):
    for p in range(3,40000,2):
        if (p-1)%k or not isprime(p): continue
        N=p*k
        if N<15168 or N>30000: continue
        r=pow(primroot(p),(p-1)//k,p)
        assert pow(r,k,p)==1 and r!=1
        out.append((N,p,k,r))
for t in sorted(out): print("N=%d p=%d k=%d r=%d"%t)
