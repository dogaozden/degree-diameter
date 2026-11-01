import math
def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
def order(r,p):
    x=r%p; k=1
    while x!=1:
        x=x*r%p; k+=1
    return k
lo,hi=5506489,5560000
out=[]
for k in [45,47,49,51,53,55,57,59,61,63]:
    for p in range(lo//k, hi//k+2):
        N=p*k
        if N<lo or N>hi: continue
        if not isprime(p): continue
        if (p-1)%k: continue
        # r of order exactly k
        rs=[r for r in range(2,p) if pow(r,k,p)==1 and order(r,p)==k]
        if not rs: continue
        # pick smallest r, and also one other
        out.append((N,p,k,rs[0],len(rs)))
for o in sorted(out): print(*o)
