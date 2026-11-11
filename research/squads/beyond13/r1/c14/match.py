import math,sys
sys.path.insert(0,'/home/user/degree-diameter/research/frontier/beyond13')
def W(d,D):
    return 1+sum(d*(d-1)**(2*i-1) for i in range(1,(D-1)//2+1))
def isprime(x):
    if x<2: return False
    i=2
    while i*i<=x:
        if x%i==0: return False
        i+=1
    return True
d,D=5,13
w=W(d,D)
for n in [1,7,13,31,97]:
    for fam in ['sl','psl']:
        best=None
        for p in range(5,400):
            if not isprime(p) or math.gcd(p,n)!=1: continue
            base=p*(p*p-1) if fam=='sl' else p*(p*p-1)//2
            N=base*n
            mu=N*math.exp(-w/N) if N>w/50 else 1e-30
            if best is None or abs(math.log(mu/3))<abs(math.log(best[2]/3)): best=(p,N,mu)
        if best: print(fam,best[0],n,'N=',best[1],'mu=%.2f'%best[2], 'vertices=',2*best[1])
