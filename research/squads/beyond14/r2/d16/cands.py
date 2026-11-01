import math
def isprime(p):
    if p<2: return False
    i=2
    while i*i<=p:
        if p%i==0: return False
        i+=1
    return True
out=[]
for p in range(190,380):
    if not isprime(p): continue
    for kind in ("sl","psl"):
        order = p*(p*p-1) if kind=="sl" else p*(p*p-1)//2
        for n in range(20,90):
            if math.gcd(n,p)!=1: continue
            N=order*n
            if 862_000_000<=N<=880_000_000:
                out.append((kind,p,n,N))
if __name__=="__main__":
    for o in out: print(*o)
    print(len(out))
