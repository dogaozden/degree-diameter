# enumerate Frobenius groups Z_p x| Z_k with N = p*k in [262081, 268000], k in 13..63, and prime p = 1 mod k
import sys
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
lo,hi=262081,268000
out=[]
for k in range(13,64):
    for p in range(lo//k, hi//k+2):
        if p*k<lo or p*k>hi: continue
        if not isprime(p) or (p-1)%k: continue
        # r of order exactly k mod p: take smallest generator-power
        for g in range(2,p):
            r=pow(g,(p-1)//k,p)
            if order_mod(r,p)==k:
                out.append((p*k,p,k,r)); break
out.sort()
for N,p,k,r in out: print(N,p,k,r)
