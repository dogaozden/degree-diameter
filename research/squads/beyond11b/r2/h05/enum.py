def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
def order(r,p):
    x=r%p; k=1
    while x!=1:
        x=x*r%p; k+=1
    return k
cands=[]
for p in range(3,20000):
    if not isprime(p): continue
    for k in range(3,p,2):
        if (p-1)%k: continue
        if not isprime(k) and k>1:
            pass
        # need element r of order exactly k mod p
        ok=None
        for r in range(2,p):
            if order(r,p)==k: ok=r; break
        if ok is None: continue
        F=p*k
        for base,name in [(120,'SL25'),(24,'SL23'),(336,'SL27'),(720,'SL29')]:
            N=base*F
            if 150601<=N<=160000:
                cands.append((N,name,p,k,ok,F))
for c in sorted(cands): print(c)
