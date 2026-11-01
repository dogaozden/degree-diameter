import math
def isprime(x):
    if x<2: return False
    i=2
    while i*i<=x:
        if x%i==0: return False
        i+=1
    return True
lo,hi=231421,330000
out=[]
for p in range(11,400):
    if not isprime(p): continue
    for fam,base in (("sl",p*(p*p-1)),("psl",p*(p*p-1)//2)):
        for n in [1]+[q for q in range(7,60) if isprime(q) and q%3==1]:
            if math.gcd(p,n)!=1: continue
            N=base*n
            if N<lo or N>hi: continue
            out.append((N,fam,p,n))
out.sort()
for N,fam,p,n in out: print(fam,p,n,N,2*N)
