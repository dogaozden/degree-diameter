import math,sys
def isprime(x):
    if x<2: return False
    i=2
    while i*i<=x:
        if x%i==0: return False
        i+=1
    return True
d,D=11,9
h=4
W=1+sum(d*(d-1)**(2*i-1) for i in range(1,h+1))
lo,hi=8661577,16000000
out=[]
for p in range(5,1200):
    if not isprime(p): continue
    if (p-1)%5 and (p+1)%5: continue
    for fam,base in (("sl",p*(p*p-1)),("psl",p*(p*p-1)//2)):
        for n in range(1,2000):
            if n>1 and not (isprime(n) and n%5==1): continue
            if math.gcd(p,n)!=1: continue
            N=base*n
            if N<lo: continue
            if N>hi: break
            mu=N*math.exp(-W/N)
            out.append((mu,fam,p,n,N))
out.sort()
for mu,fam,p,n,N in out[:60]: print(f"{fam} {p} {n} N={N} 2N={2*N} mu={mu:.2f}")
print(len(out))
