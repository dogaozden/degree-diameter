import sys
def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
# odd Frobenius Z_m x|_r Z_k: m prime, k odd prime, k | m-1, r of order k mod m
groups=[]
for k in range(3,60,2):
    if not isprime(k): continue
    for m in range(k+1,4000):
        if not isprime(m) or (m-1)%k: continue
        # find r of order k
        r=None
        for x in range(2,m):
            if pow(x,k,m)==1 and x!=1:
                r=x; break
        if r is None: continue
        if m*k>2000: continue
        groups.append((m*k,m,k,r))
groups.sort()
lo,hi=148900,160000
out=[]
for o1,m1,k1,r1 in groups:
    for o2,m2,k2,r2 in groups:
        if o1>o2: continue
        P=o1*o2
        if lo<=P<=hi:
            out.append((P,o1,m1,k1,r1,m2,k2,r2))
out.sort()
for t in out: print(*t)
print("count",len(out), file=sys.stderr)
