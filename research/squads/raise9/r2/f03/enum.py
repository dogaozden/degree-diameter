import sys
from math import prod
def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
def order(r,m):
    x=r%m; o=1
    while x!=1%m:
        x=x*r%m; o+=1
    return o
lo,hi=int(sys.argv[1]),int(sys.argv[2])
out=[]
for m in range(3,hi):
    if not isprime(m): continue
    for k in range(3,hi//m+1,2):
        if m*k<lo or m*k>hi: continue
        if (m-1)%k: continue
        # find r of order exactly k mod m
        r=None
        for c in range(2,m):
            if order(c,m)==k: r=c; break
        if r is None: continue
        # r is one generator of the subgroup of order k? pick minimal: any element of order k generates subgroup; need subgroup choice
        out.append((m*k,m,k,r))
for N,m,k,r in sorted(out):
    print(N,m,k,r,"meta",m,k,r)
