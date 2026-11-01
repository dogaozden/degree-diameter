import sys, math
def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
def primroot(p):
    fac=[q for q in range(2,p) if (p-1)%q==0 and isprime(q)]
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac): return g
G={}
for p in range(3,400):
    if not isprime(p): continue
    g=primroot(p)
    for k in range(2,min(p,200)):
        if (p-1)%k: continue
        r=pow(g,(p-1)//k,p)   # order exactly k
        G.setdefault(p*k,[]).append((p,k,r))
lo,hi=int(sys.argv[1]),int(sys.argv[2])
pairs=[]
orders=sorted(G)
for a in orders:
    if a*a>hi: break
    for b in orders:
        if b<a: continue
        if a*b>hi: break
        if a*b>=lo:
            for g1 in G[a]:
                for g2 in G[b]:
                    pairs.append((a*b,g1,g2))
pairs.sort()
print(len(pairs))
for t in pairs: print(t)
