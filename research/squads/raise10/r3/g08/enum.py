import sys
def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
Qs={'psl 3':12,'sl 3':24,'meta 7 3 2':21,'meta 13 3 3':39}
LO,HI=262081,265000
out=[]
for Q,qs in Qs.items():
    for k in range(13,46,2):
        for p in range(3,2000):
            if not isprime(p) or (p-1)%k: continue
            m=qs*p*k
            if not (LO<=m<=HI): continue
            # find r of order exactly k mod p (Frobenius: fixed-point-free)
            rs=[r for r in range(2,p) if pow(r,k,p)==1 and all(pow(r,k//q,p)!=1 for q in range(2,k+1) if k%q==0 and isprime(q))]
            if not rs: continue
            out.append((m,Q,p,k,rs[0]))
for m,Q,p,k,r in sorted(out):
    print(m,Q,'x meta',p,k,r)
