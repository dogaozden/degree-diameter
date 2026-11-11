import sys
def isprime(p):
    if p<2: return False
    i=2
    while i*i<=p:
        if p%i==0: return False
        i+=1
    return True
out=[]
for q in range(3,400):
    if not isprime(q): continue
    sl=q*(q*q-1)
    psl=sl//2 if q>2 else None
    for name,order in (("sl",sl),("psl",psl)):
        if order is None: continue
        for n in range(1,80):
            N=order*n
            if 6552899 < N <= 6750000:
                out.append((N,name,q,n))
out.sort()
for r in out: print(*r)
