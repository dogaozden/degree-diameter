# metacyclic F = Z_m x|_r Z_k (r^k = 1 mod m, m k in range), Q = Z7 x|2 Z3 (21): N = 21*m*k in [6209, 6500]
res=[]
for Qo,qn in [(21,'meta 7 3 2'),(39,'meta 13 3 3'),(57,'meta 19 3 7'),(55,'meta 11 5 3')]:
    lo=-(-6209//Qo); hi=6500//Qo
    for m in range(3,hi+1):
        for k in range(2,hi//m+1):
            if m*k<lo or m*k>hi: continue
            for r in range(2,m):
                if pow(r,k,m)==1 and m % 2 == 1 and gcd_ok if False else pow(r,k,m)==1:
                    # require r to be nontrivial (non-abelian) and gcd(r-1,m) small to avoid trivial
                    if r % m == 1: continue
                    if r == 0: continue
                    from math import gcd
                    if gcd(m, k) != 1 and False: continue
                    res.append((qn,Qo*m*k,m,k,r)); break
seen=set()
for t in sorted(res,key=lambda x:x[1]):
    if t[0]!=('meta 7 3 2') : continue
    print(t)
