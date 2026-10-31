import sys
def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
def ispp(q):
    # prime power
    if q<2: return False
    for p in range(2,q+1):
        if isprime(p):
            x=q
            while x%p==0: x//=p
            return x==1
    return False
lo,hi=47881,49000
res=[]
for q in range(3,400):
    if not isprime(q): continue  # primes only (haar_sd psl/sl q prime or prime power; keep primes)
    for name,o in (("psl",q*(q*q-1)//2),("sl",q*(q*q-1)),("pgl",q*(q*q-1))):
        if o>hi: continue
        # n such that o*n in [lo,hi]
        n=-(-lo//o)
        while o*n<=hi:
            if o*n>=lo: res.append((o*n,name,q,n,o))
            n+=1
for r in sorted(res)[:200]: print(*r)
print("total",len(res))
