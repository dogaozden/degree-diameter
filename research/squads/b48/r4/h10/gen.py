import sys
from math import gcd
def metas(N):
    out=[]
    for m in range(1,N+1):
        if N % m: continue
        k=N//m
        for r in range(1,m+1):
            if gcd(r,m)!=1 and m>1: continue
            if m>1 and pow(r,k,m)!=1%m: continue
            if m==1 and r!=1: continue
            if r==1 and m>1 and k>1: continue  # abelian, keep only cyc form below
            out.append((m,k,r))
    return out
# order of r mod m must be >1 (nonabelian) ; keep up to 3 per order preferring larger k
def pick(N, cap=3):
    cands=[c for c in metas(N) if c[1]>1 and c[2]!=1 and c[0]>1]
    # prefer dihedral-like (k=2) and mid k
    cands.sort(key=lambda c:(c[1]!=2, -c[1]))
    seen=[]; 
    for c in cands:
        if c not in seen: seen.append(c)
    return seen[:cap]
spec=[]
plan={
 'heawood':(14,[37,38,39,40,42]),
 'moebius_kantor':(16,[32,34,36]),
 'pappus':(18,[29,30,32]),
 'desargues':(20,[26,27,28]),
 'tutte8':(30,[17,18,20]),
}
for base,(b,Ns) in plan.items():
    for N in Ns:
        spec.append((base,b,f"meta:{N}:1:1"))
        for (m,k,r) in pick(N, 2 if N>36 else 3):
            spec.append((base,b,f"meta:{m}:{k}:{r}"))
for s in spec: print(*s)
