def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
def pf(n):
    s=set(); i=2
    while i*i<=n:
        while n%i==0: s.add(i); n//=i
        i+=1
    if n>1: s.add(n)
    return s
ks=[23,25,27,29,31,33,35,37,39,45,51,57,63]
for k in ks:
    qs=pf(k)
    for p in range(155250//k, 165001//k+2):
        if not isprime(p) or (p-1)%(2*k)!=0: continue
        N=p*k
        if N<155250 or N>165000: continue
        found=None
        for g in range(2,p):
            r=pow(g,(p-1)//k,p)
            if pow(r,k,p)==1 and all(pow(r,k//q,p)!=1 for q in qs):
                found=r; break
        print(k,p,N,found)
