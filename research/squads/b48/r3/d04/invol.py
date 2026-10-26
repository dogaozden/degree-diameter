import sys
from math import gcd
lines=[l.split() for l in open('cands.txt')]
res=[]
for N,m,k,r,g in [(int(a),int(b),int(c),int(d),int(e)) for a,b,c,d,e in lines]:
    inv=0
    for j in range(k):
        if (2*j)%k: continue
        rj=pow(r,j,m)
        # elements (a,j) with (1+r^j)a = 0 mod m, excluding identity
        cnt=gcd((1+rj)%m, m)
        if j==0: cnt-=1
        inv+=cnt
    res.append((inv,N,m,k,r,g))
res.sort()
for row in res: print(*row)
