import sys
def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
def prim_root(p):
    fs=[q for q in range(2,p) if (p-1)%q==0 and isprime(q)]
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g
    return 1
lo,hi=6209,6600
out=[]
for p in range(3,hi+1):
    if not isprime(p): continue
    for k in range(2,hi//p+1):
        if (p-1)%k: continue
        N=p*k
        if N<lo or N>hi: continue
        g=prim_root(p)
        r=pow(g,(p-1)//k,p)
        # order check
        o=1; x=r
        while x!=1: x=x*r%p; o+=1
        if o!=k: continue
        out.append((N,p,k,r))
out.sort()
for N,p,k,r in out: print(N,p,k,r, "even" if k%2==0 else "odd")
print(len(out), file=sys.stderr)
