import sys
def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
def primefactors(n):
    f=set(); d=2
    while d*d<=n:
        while n%d==0: f.add(d); n//=d
        d+=1
    if n>1: f.add(n)
    return f
def primroot(m):
    ps=primefactors(m-1)
    for g in range(2,m):
        if all(pow(g,(m-1)//p,m)!=1 for p in ps): return g
lo,hi=int(sys.argv[1]),int(sys.argv[2])
out=[]
for m in range(3,hi):
    if m*3>hi: break
    if not isprime(m): continue
    g=None
    for k in range(3,hi//m+1,2):
        if m*k<lo or m*k>hi: continue
        if (m-1)%k: continue
        if g is None: g=primroot(m)
        r=pow(g,(m-1)//k,m)   # element of order exactly k
        out.append((m*k,m,k,r))
for N,m,k,r in sorted(out):
    print(N,m,k,r,"  meta",m,k,r, flush=True)
