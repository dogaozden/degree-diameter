# enumerate products for (6,9) and (7,9): G = F1 x F2, N = |G|
import sys
def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
def primerange(a,b): return [x for x in range(a,b) if isprime(x)]
def order(r,p):
    x=r%p; k=1
    while x!=1: x=x*r%p; k+=1
    return k
def frob(p):
    out=[]
    for k in range(3,64,2):
        if (p-1)%k: continue
        for r in range(2,p):
            if order(r,p)==k:
                out.append((k,r)); break
    return out
lo,hi=int(sys.argv[1]),int(sys.argv[2])
facs={'sl5':120,'m73':21,'m133':39,'m193':57}
rows=[]
for p in primerange(5,3000):
    for k,r in frob(p):
        rows.append((p*k,p,k,r))
for name,o in facs.items():
    for (m,p,k,r) in rows:
        N=o*m
        if lo<=N<=hi: print(N,name,p,k,r)
fr=[(m,p,k,r) for (m,p,k,r) in rows if m<=4000]
for a in [(21,7,3,2),(39,13,3,3),(57,19,3,7)]:
    for (m,p,k,r) in fr:
        N=a[0]*m
        if lo<=N<=hi and p!=a[1]: print(N,'F%d_%d'%(a[0],a[1]),p,k,r)
