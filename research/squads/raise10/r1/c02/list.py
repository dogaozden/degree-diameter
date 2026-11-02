import math,sys
sys.path.insert(0,'/home/user/degree-diameter/research/frontier/raise10')
def isprime(x):
    if x<2: return False
    i=2
    while i*i<=x:
        if x%i==0: return False
        i+=1
    return True
def okn(n,k=5):
    if n==1: return True
    m=n;q=2
    while q*q<=m:
        if m%q==0:
            if q%k!=1: return False
            while m%q==0: m//=q
        q+=1
    return m==1 or m%k==1
T=166398649
out=[]
for fam,lo,hi,nmax in [('psl',230,700,60),('sl',60,200,200)]:
    for p in range(lo,hi+1):
        if not isprime(p) or ((p-1)%5 and (p+1)%5): continue
        base=p*(p*p-1)//(2 if fam=='psl' else 1)
        for n in range(1,nmax+1):
            if math.gcd(n,p)!=1 or not okn(n): continue
            N=base*n
            if N>=T and N<=T*1.3: out.append((N,fam,p,n))
out.sort()
for N,fam,p,n in out[:40]: print(fam,p,n,N,2*N)
