def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
def order(r,m):
    x,k=r%m,1
    while x!=1: x=x*r%m; k+=1
    return k
out=[]
for k in range(9,200,2):
    if isprime(k): continue
    for p in range(3,4000):
        if not isprime(p) or (p-1)%k: continue
        N=p*k
        if not (15168<=N<=19000): continue
        for g in range(2,p):
            r=pow(g,(p-1)//k,p)
            if order(r,p)==k: break
        out.append((N,p,k,r))
for t in sorted(out): print(*t)
