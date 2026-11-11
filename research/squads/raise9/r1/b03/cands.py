import math
def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
d,D=13,9
W=1+sum(d*(d-1)**(2*i-1) for i in range(1,5))
print("W",W)
out=[]
for p in range(5,400):
    if not isprime(p): continue
    for fam,base in (("sl",p*(p*p-1)),("psl",p*(p*p-1)//2)):
        for n in range(1,40):
            if math.gcd(p,n)!=1: continue
            N=base*n
            if N<33_871_345 or N>40_000_000: continue
            mu=N*math.exp(-W/N)
            out.append((mu,fam,p,n,N))
out.sort()
for mu,fam,p,n,N in out[:60]:
    print(f"{fam} p={p} n={n} N={N} 2N={2*N} mu={mu:.2f} torus~{p*math.exp(-W/N/3):.2f} central~{2*n*math.exp(-W/N/4):.2f}")
