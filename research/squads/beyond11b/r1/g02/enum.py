def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
def primefactors(n):
    s=set();i=2
    while i*i<=n:
        while n%i==0: s.add(i); n//=i
        i+=1
    if n>1: s.add(n)
    return s
out=[]
for m in range(3,20001,2):
    if not isprime(m): continue
    for k in range(9,400,2):
        N=m*k
        if N<12181 or N>20000 or (m-1)%k: continue
        ps=primefactors(k)
        r=None
        for a in range(2,m):
            if pow(a,k,m)==1 and all(pow(a,k//p,m)!=1 for p in ps):
                r=a;break
        if r is None: continue
        out.append((N,m,k,r))
out.sort()
for t in out: print(*t)
