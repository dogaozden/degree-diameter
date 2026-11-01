import sys
def isprime(x):
    if x<3: return x==2
    if x%2==0: return False
    i=3
    while i*i<=x:
        if x%i==0: return False
        i+=2
    return True
def order(r,m):
    o=1; x=r%m
    while x!=1%m:
        x=x*r%m; o+=1
    return o
out=[]
LO,HI=242000,270000
for k in range(13,40):
    for m in range(LO//k, HI//k+1):
        if not isprime(m) or (m-1)%k: continue
        N=m*k
        if not (LO<=N<=HI): continue
        # elements r of order exactly k mod m
        for x in range(2,200):
            r=pow(x,(m-1)//k,m)
            if r!=1 and order(r,m)==k:
                out.append((N,m,k,r)); break
for t in sorted(out): print(*t)
