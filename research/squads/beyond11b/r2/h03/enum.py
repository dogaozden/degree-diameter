import math
def isprime(x):
    if x<2: return False
    i=2
    while i*i<=x:
        if x%i==0: return False
        i+=1
    return True
def frob(m,k):
    # all r with r^k=1 mod m, r order exactly k, m prime, k odd>1, k|m-1
    out=[]
    if not isprime(m) or k<=1 or k%2==0 or (m-1)%k: return out
    g=[r for r in range(2,m) if pow(r,k,m)==1 and r!=1]
    return g[:1]
# all Frobenius-type F = Z_p x| Z_k (p prime, k odd, k | p-1) with order p*k
F={}
for p in range(3,2000):
    if not isprime(p): continue
    for k in range(3,400,2):
        if (p-1)%k==0:
            F.setdefault(p*k,[]).append((p,k,frob(p,k)[0]))
# meta 7 3 2 : Z7 x| Z3 order 21
out=[]
for name,base,lo,hi in (("sl3",24,14460,17000),("sl5",120,14460,17000),("F7_3",21,14460,17000)):
    for order,lst in F.items():
        N=base*order
        if lo<=N<=hi:
            for (p,k,r) in lst:
                out.append((N,name,p,k,r,order))
for N,name,p,k,r,order in sorted(out):
    print(N,name,"meta",p,k,r,"|F|=",order)
