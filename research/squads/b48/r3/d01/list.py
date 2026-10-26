# enumerate Frobenius-type metacyclic Z_p x| Z_k, k | p-1, N=p*k in [2486,2900]
def isprime(n):
    return n>1 and all(n%q for q in range(2,int(n**0.5)+1))
def order_mod(r,p):
    x,k=r%p,1
    while x!=1:
        x=x*r%p; k+=1
    return k
out=[]
for p in range(3,2900):
    if not isprime(p): continue
    for k in range(2,p):
        if (p-1)%k: continue
        N=p*k
        if N<2486 or N>2900: continue
        # primitive-ish: find r of order exactly k mod p
        rs=[r for r in range(2,p) if order_mod(r,p)==k]
        if not rs: continue
        r=min(rs)
        out.append((N,p,k,r,len(rs)))
for N,p,k,r,c in sorted(out):
    print(N, f"meta {p} {k} {r}", "phi_k_roots", c, "n=",2*N)
