import math,sys
def W(d,D):
    return 1+sum(d*(d-1)**(2*i-1) for i in range(1,(D-1)//2+1))
d,D=13,9
w=W(d,D)
def isprime(x):
    return x>1 and all(x%k for k in range(2,int(x**0.5)+1))
bar=33871345
rows=[]
for p in range(89,142):
    if not isprime(p): continue
    for fam,base in (("sl",p*(p*p-1)),("psl",p*(p*p-1)//2)):
        for n in range(1,60):
            if math.gcd(p,n)!=1: continue
            N=base*n
            if N<bar or N>40e6: continue
            mu=N*math.exp(-w/N)
            r3=sum(1 for r in range(2,n) if math.gcd(r,n)==1 and pow(r,3,n)==1) if n>1 else 0
            rows.append((N,fam,p,n,round(mu,2),r3))
for r in sorted(rows): print(r)
