import sys
def prim_root(p):
    fac=[]; n=p-1; q=2
    while q*q<=n:
        if n%q==0:
            fac.append(q)
            while n%q==0: n//=q
        q+=1
    if n>1: fac.append(n)
    for g in range(2,p):
        if all(pow(g,(p-1)//f,p)!=1 for f in fac): return g
def rfor(p,k):
    g=prim_root(p); r=pow(g,(p-1)//k,p)
    assert pow(r,k,p)==1 and all(pow(r,j,p)!=1 for j in range(1,k))
    return r
if __name__=="__main__":
    p,k=int(sys.argv[1]),int(sys.argv[2]); print(rfor(p,k))
