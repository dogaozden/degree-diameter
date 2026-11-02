import math,sys
def isprime(x):
    if x<2: return False
    i=2
    while i*i<=x:
        if x%i==0: return False
        i+=1
    return True
def has5(n):
    if n==1: return True
    # exists r != 1 with r^5 == 1 mod n, gcd(r,n)=1
    for r in range(2,n):
        if math.gcd(r,n)==1 and pow(r,5,n)==1: return True
    return False
lo,hi=float(sys.argv[1]),float(sys.argv[2])
rows=[]
for p in range(7,1200):
    if not isprime(p): continue
    if p%5 not in (1,4): continue
    for fam in ('sl','psl'):
        g = p*(p*p-1)//(2 if fam=='psl' else 1)
        for n in range(1,400):
            N=g*n
            if 2*N<lo or 2*N>hi: 
                if 2*N>hi: break
                continue
            if math.gcd(n,p)!=1: continue
            if not has5(n): continue
            rows.append((2*N,fam,p,n))
rows.sort()
for r in rows: print(f"{r[1]} p={r[2]} n={r[3]} 2N={r[0]} N={r[0]//2}")
print(len(rows))
