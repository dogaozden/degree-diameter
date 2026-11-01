# two Frobenius factors, each with k >= 5, N = m1*m2 in window
import sys
def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
def order(r,p):
    x=r%p; k=1
    while x!=1: x=x*r%p; k+=1
    return k
lo,hi=int(sys.argv[1]),int(sys.argv[2])
fr=[]
for p in range(5,3000):
    if not isprime(p): continue
    for k in range(5,64,2):
        if (p-1)%k: continue
        for r in range(2,p):
            if order(r,p)==k: fr.append((p*k,p,k,r)); break
fr=[f for f in fr if f[0]<=hi]
out=[]
for a in fr:
    for b in fr:
        if a[1]>=b[1]: continue
        N=a[0]*b[0]
        if lo<=N<=hi: out.append((N,a,b))
for N,a,b in sorted(out): print(N,'F',a[1],a[2],a[3],'F',b[1],b[2],b[3])
