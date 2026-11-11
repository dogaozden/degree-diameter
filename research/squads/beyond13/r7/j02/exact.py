import math
def primes_of(n):
    ps=[];p=2
    while p*p<=n:
        if n%p==0:
            ps.append(p)
            while n%p==0: n//=p
        p+=1
    if n>1: ps.append(n)
    return ps
def isprime(x):
    if x<2: return False
    i=2
    while i*i<=x:
        if x%i==0: return False
        i+=1
    return True
res=[]
for line in open('enum_out.txt'):
    if not line.startswith('('): continue
    N,m,k,c,ip=eval(line)
    # exact-order r with order k
    best=None
    for r in range(2,m):
        if math.gcd(r,m)!=1 or pow(r,k,m)!=1: continue
        if all(pow(r,k//p,m)!=1 for p in primes_of(k)):
            best=r;break
    if best is None: continue
    # center: trivial iff r has order k (for m prime) ; for composite m check order of r mod each prime
    res.append((N,m,k,best,ip))
res.sort()
for x in res: print(x)
print(len(res))
