# enumerate (family, q, n) with N = |Q| * n in [1094,1400], all prime factors of n = 1 mod 3 (or n = 1), 3 | |Q|
from math import gcd
def isprime_pow(q):
    for p in range(2,q+1):
        if q%p==0:
            while q%p==0: q//=p
            return q==1
    return False
def factor(n):
    f={};d=2
    while d*d<=n:
        while n%d==0: f[d]=f.get(d,0)+1; n//=d
        d+=1
    if n>1: f[n]=f.get(n,0)+1
    return f
out=[]
for q in range(2,40):
    if not isprime_pow(q): continue
    sl=q*(q*q-1)
    fams={'sl':sl,'pgl':sl,'psl':sl//gcd(2,q-1)}
    for fam,Q in fams.items():
        if fam=='psl' and q%2==0: continue  # same as sl
        if Q%3: continue
        for n in range(1,1400):
            if not (1094<=Q*n<=1400): continue
            if n>1 and not all(p%3==1 for p in factor(n)): continue
            out.append((Q*n,fam,q,Q,n))
for x in sorted(out): print(x)
