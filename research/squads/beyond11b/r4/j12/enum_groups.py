def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
def factors(n):
    f=[];d=2
    while d*d<=n:
        while n%d==0: f.append(d); n//=d
        d+=1
    if n>1: f.append(n)
    return set(f)
def primroot(p):
    fs=factors(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g
cands=[]
for k in [35,37,39,41,43,45,47]:
    for p in range(2,400000):
        if p % (2*k) != 1 or not isprime(p): continue
        N=p*k
        if 155250 <= N <= 170000:
            g=primroot(p)
            r=pow(g,(p-1)//k,p)
            ok=all(pow(r,k//q,p)!=1 for q in factors(k))
            cands.append((k,p,N,r,ok))
for c in cands: print(*c)
print(len(cands))
