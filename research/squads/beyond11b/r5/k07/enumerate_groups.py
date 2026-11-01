lo,hi=1056058,1065000
def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
def order(r,p):
    x=r; o=1
    while x!=1:
        x=x*r%p; o+=1
    return o
out=[]
for k in range(33,64,2):
    for p in range(lo//k, hi//k+2):
        N=p*k
        if N<lo or N>hi or (p-1)%k or not isprime(p): continue
        # find r of exact order k
        r=None
        for a in range(2,p):
            if pow(a,(p-1)//k,p)!=1 and True:
                cand=pow(a,(p-1)//k,p)
                if order(cand,p)==k: r=cand; break
        if r is None: 
            # fallback search
            continue
        out.append((N,p,k,r))
out.sort()
for N,p,k,r in out: print(N,p,k,r)
print(len(out))
