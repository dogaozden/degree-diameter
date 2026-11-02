import math
def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
def order_mod(r,p):
    x=r%p; o=1
    while x!=1:
        x=x*r%p; o+=1
    return o
def frob(lo,hi,kmin=3,kmax=63,odd=True):
    res=[]
    for k in range(kmin,kmax+1):
        if odd and k%2==0: continue
        for p in range(max(2,lo//k), hi//k+2):
            if p*k<lo or p*k>hi or not isprime(p) or (p-1)%k: continue
            for g in range(2,p):
                r=pow(g,(p-1)//k,p)
                if order_mod(r,p)==k: res.append((p*k,p,k,r)); break
    return res
small=[(21,7,3,2),(39,13,3,3),(57,19,3,7),(55,11,5,3),(93,31,3,5),(65,13,5,None)]
small=[(21,7,3,2),(39,13,3,3),(57,19,3,7)]
out=[]
for N1,p1,k1,r1 in small:
    lo=math.ceil(262081/N1); hi=268000//N1
    for N2,p2,k2,r2 in frob(lo,hi):
        if math.gcd(N1,N2)!=1: continue
        out.append((N1*N2,N1,p1,k1,r1,N2,p2,k2,r2))
out.sort()
for o in out: print(*o)
