from math import gcd
import collections
def order_r(r,m,k):
    x=1%m; o=0
    while True:
        x=x*r%m; o+=1
        if x==1%m: return o
cands=[]
for N in range(1121,1251):
    for k in range(6, N//3+1):
        if N % k: continue
        m = N//k
        if m < 2: continue
        seen=set()
        for r in range(1,m):
            if gcd(r,m)!=1: continue
            if pow(r,k,m)!=1%m: continue
            o=order_r(r,m,k)
            if o<6: continue
            g=gcd(r-1,m)
            if g>2: continue
            canon=min(pow(r,j,m) for j in range(1,k+1) if gcd(j,k)==1) if m>1 else r
            if canon in seen: continue
            seen.add(canon)
            cands.append((N,m,k,canon,o,g))
print(len(cands))
# summary by ord
c=collections.Counter(c[4] for c in cands); print(sorted(c.items()))
# preferred: ord in (6,10,12,20), g==1
pref=[c for c in cands if c[4] in (6,10,12,20) and c[5]==1]
print("pref",len(pref))
for c in pref[:80]: print(c)
