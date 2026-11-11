import math
W = 1 + sum(5*4**(2*i-1) for i in range(1,6))
def isprime(x):
    if x<2: return False
    i=2
    while i*i<=x:
        if x%i==0: return False
        i+=1
    return True
out=[]
for p in range(5,200):
    if not isprime(p): continue
    for fam,base in (("sl",p*(p*p-1)),("psl",p*(p*p-1)//2)):
        for n in range(1,800):
            if math.gcd(p,n)!=1: continue
            N=base*n
            if N<148000 or N>175000: continue
            # need an element r with r^3=1 mod n (r any), n fine
            mu=N*math.exp(-W/N)
            out.append((mu,fam,p,n,N))
out.sort()
for mu,fam,p,n,N in out:
    if mu>=8 and mu<=30:
        f = [r for r in range(1,n+1) if math.gcd(r,n)==1 and pow(r,3,n)==1] if n>1 else [1]
        print(f"mu={mu:.2f} {fam} p={p} n={n} N={N} 2N={2*N} r3={len(f)}")
