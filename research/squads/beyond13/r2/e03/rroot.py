import sys
def factor(n):
    f=[];x=n;q=2
    while q*q<=x:
        while x%q==0: f.append(q); x//=q
        q+=1
    if x>1: f.append(x)
    return set(f)
def primroot(p):
    fs=factor(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g
p,k=int(sys.argv[1]),int(sys.argv[2])
g=primroot(p); r=pow(g,(p-1)//k,p)
assert pow(r,k,p)==1 and r!=1
print(r)
