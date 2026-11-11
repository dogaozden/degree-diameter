import math,sys
def W(d,D):
    return 1+sum(d*(d-1)**(2*i-1) for i in range(1,(D-1)//2+1))
def isprime(x):
    if x<2: return False
    i=2
    while i*i<=x:
        if x%i==0: return False
        i+=1
    return True
def order5_unit(n):
    # exists r with r^5=1 mod n, r!=1 mod n (or n==1 trivially ok)
    if n==1: return True
    for r in range(2,n):
        if math.gcd(r,n)==1 and pow(r,5,n)==1 and math.gcd(r-1,n)<=2: return True
    return False
w=W(10,9); out=[]
for p in range(5,400):
    if not isprime(p): continue
    if (p-1)%5 and (p+1)%5: continue
    for fam,base in (("sl",p*(p*p-1)),("psl",p*(p*p-1)//2)):
        for n in range(1,400):
            if math.gcd(p,n)!=1: continue
            N=base*n
            if N<4209061: continue
            if N>1.1e7: break
            mu=N*math.exp(-w/N)
            if mu>130: break
            if n>1 and (not order5_unit(n) or n%2==0 or not (n>1)): continue
            out.append((mu,fam,p,n,N))
out.sort()
for mu,fam,p,n,N in out[:60]: print(f"{fam} {p} {n} N={N} 2N={2*N} mu={mu:.2f} isprime_n={isprime(n)}")
