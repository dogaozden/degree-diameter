import math,sys
def isprime(x):
    if x<2: return False
    i=2
    while i*i<=x:
        if x%i==0: return False
        i+=1
    return True
lo,hi=208321,260000
out=[]
for p in range(5,400):
    if not isprime(p): continue
    for fam,base in (("sl",p*(p*p-1)),("psl",p*(p*p-1)//2)):
        for n in [1]+[q for q in range(7,2000) if isprime(q) and q%3==1]:
            if math.gcd(p,n)!=1: continue
            N=base*n
            if N<lo: continue
            if N>hi: break
            out.append((N,fam,p,n))
out.sort()
for N,fam,p,n in out: print(fam,p,n,N,2*N)
