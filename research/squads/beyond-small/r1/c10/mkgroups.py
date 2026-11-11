import sys, random
sys.path.insert(0,'/home/user/degree-diameter/research/squads/beyond-small/r1/c10')
from math import gcd
from mzgrp import valid
out=[]
for N in range(16897, 20001):
    for k in range(2, N+1):
        if N % k: continue
        n = N//k
        if n < 3: continue
        units = [x for x in range(1,n) if gcd(x,n)==1]
        us = [u for u in range(1,n) if gcd(u,n)==1 and (u*u)%n==1]
        vs = [v for v in range(1,k) if gcd(v,k)==1 and (v*v)%k==1]
        if not us or not vs: continue
        for r in units:
            if r==1 or pow(r,k,n)!=1: continue
            for v in vs:
                if pow(r,v,n)!=r%n: continue
                for u in us:
                    out.append((N,n,k,r,u,v))
import collections
c=collections.Counter(x[0] for x in out)
print(len(out), len(c))
random.seed(1)
random.shuffle(out)
with open('/home/user/degree-diameter/research/squads/beyond-small/r1/c10/groups_all.txt','w') as f:
    for t in out: f.write("%d %d %d %d %d %d\n" % (t[1],t[2],t[3],t[4],t[5],t[0]))
