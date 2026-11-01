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
# odd-order metacyclic groups (m,k,r) with r of exact order k, orders 21..1000
G=[]
for k in (5,7,9,11,13,15,17,19,21,25,27,29,31,33,35,37,39,41,43,45,47,49):
    for m in range(3,1200,2):
        if m*k>1000: break
        if math.gcd(m,k)>1 and False: pass
        for r in range(2,m):
            if math.gcd(r,m)!=1 or pow(r,k,m)!=1: continue
            if all(pow(r,k//p,m)!=1 for p in primes_of(k)):
                G.append((m*k,m,k,r)); break
Gs=sorted(set(G))
print(len(Gs))
lo,hi=14879,15500
out=[]
for a in Gs:
    for b in Gs:
        if a[0]>b[0]: continue
        N=a[0]*b[0]
        if lo<=N<=hi:
            out.append((N,a,b))
out.sort()
for o in out[:60]: print(o)
print(len(out))
