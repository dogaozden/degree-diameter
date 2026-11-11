import math
def isprime(x):
    if x<2: return False
    i=2
    while i*i<=x:
        if x%i==0: return False
        i+=1
    return True
out=[]
lo,hi=5878549,6400000
for q in range(5,400):
    if not isprime(q): continue
    for fam,mult in (("psl",(q*(q*q-1))//2),("sl",q*(q*q-1))):
        n=1
        while True:
            N=mult*n
            if N>hi: break
            if N>=lo and math.gcd(q,n)==1 and (n==1 or isprime(n)):
                out.append((N,fam,q,n))
            n+=1
out=[r for r in out if r[3]<=400]; out.sort()
for r in out[:60]: print(*r)
print(len(out))
