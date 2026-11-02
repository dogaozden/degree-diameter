from math import gcd
def order_mod(r,m):
    x=1
    for k in range(1,m+1):
        x=x*r%m
        if x==1: return k
    return None
def sieve(n):
    s=[1]*(n+1); s[0]=s[1]=0
    for i in range(2,int(n**.5)+1):
        if s[i]:
            for j in range(i*i,n+1,i): s[j]=0
    return [i for i in range(n+1) if s[i]]
Ps=sieve(2000)
Qs={'meta 7 3 2':21,'meta 13 3 3':39,'meta 19 3 7':57,'meta 11 5 3':55}
# Frobenius F = meta p k r, k | p-1, r of order exactly k; also metacyclic meta m k r with m composite
out=[]
for qn,qo in Qs.items():
    lo=-(-6209//qo); hi=6500//qo
    for p in Ps:
        for k in range(2,p):
            if (p-1)%k or p*k<lo or p*k>hi: continue
            # r of order k mod p
            for r in range(2,p):
                if order_mod(r,p)==k:
                    out.append((qn,qo,p*k*qo,f"meta {p} {k} {r}")); break
for o in sorted(out,key=lambda t:t[2]): print(o)
