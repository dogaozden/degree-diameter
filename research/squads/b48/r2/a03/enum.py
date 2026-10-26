import sys
sys.path.insert(0, "/home/user/degree-diameter/research/squads/b48/tools")
def isprime(n):
    return n>1 and all(n%i for i in range(2,int(n**0.5)+1))
def ordm(p,d):
    x,o=p%d,1
    while x!=1:
        x=x*p%d;o+=1
    return o
out=[]
for p in range(2,200):
    if not isprime(p): continue
    for m in range(2,12):
        q=p**m
        if q>1460: break
        for k in range(3,1461):
            if q*k<1100 or q*k>1460: continue
            if k%p==0: continue
            if ordm(p,k)!=m: continue
            if (q-1)%k: continue
            out.append((q*k,p,m,k))
out.sort()
for o in out: print(o[0], f"{o[1]}:{o[3]}", f"F_{o[1]}^{o[2]}", f"Z_{o[3]}")
print(len(out))
