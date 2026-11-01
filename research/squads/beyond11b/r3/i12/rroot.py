import sys
def factor(n):
    f=[];d=2
    while d*d<=n:
        while n%d==0: f.append(d); n//=d
        d+=1
    if n>1: f.append(n)
    return set(f)
def prim_root(p):
    fs=factor(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g
def r_order(p,k):
    g=prim_root(p); r=pow(g,(p-1)//k,p)
    assert pow(r,k,p)==1
    # check exact order k
    for d in factor(k):
        if pow(r,k//d,p)==1: return None
    return r
for spec in sys.argv[1:]:
    p,k=map(int,spec.split(','))
    print(p,k,r_order(p,k))
