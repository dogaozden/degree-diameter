import sys
def isprime(n):
    if n<2: return False
    if n%2==0: return n==2
    i=3
    while i*i<=n:
        if n%i==0: return False
        i+=2
    return True
def primes_of(k):
    ps=[];p=2;x=k
    while p*p<=x:
        if x%p==0:
            ps.append(p)
            while x%p==0: x//=p
        p+=1
    if x>1: ps.append(x)
    return ps
lo,hi=int(sys.argv[1]),int(sys.argv[2])
out=[]
for k in range(13,hi//3+1):
    mlo=max(3,lo//k); mhi=hi//k
    for m in range(mlo,mhi+1):
        if (m-1)%k: continue
        if not isprime(m): continue
        N=m*k
        if not(lo<=N<=hi): continue
        found=None
        for a in range(2,60):
            r=pow(a,(m-1)//k,m)
            if r==1: continue
            if all(pow(r,k//p,m)!=1 for p in primes_of(k)):
                found=r;break
        if found: out.append((N,m,k,found))
out.sort()
for t in out[:60]: print(*t)
print("count",len(out))
