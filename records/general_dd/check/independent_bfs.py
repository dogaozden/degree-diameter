#!/usr/bin/env python3
"""independent_bfs.py WITNESSFILE : pure-python check of a finalize.py witness file (group Z_m x|_r Z_n, [x,y][u,v]=[x+u,y*r^u+v]).
Checks r^n=1 mod m, generators distinct/non-identity, group closed, BFS from identity covers all n*m with eccentricity <= D, degree."""
import sys,re
t=open(sys.argv[1]).read(); h=dict(re.findall(r'(\w+)=(\d+)',t.split('\n')[0]))
d,D,N,m,n,r=[int(h[k]) for k in ('d','D','N','m','n','r')]
S=[(int(a),int(b)) for a,b in re.findall(r'\((\d+),(\d+)\)',t.split('set:')[1])]
inv_l=re.findall(r'inv\((\d+),(\d+)\)',t)
assert N==n*m and pow(r,n,m)==1%m
rp=[pow(r,k,m) for k in range(n)]
mul=lambda a,b:((a[0]+b[0])%n,(a[1]*rp[b[0]%n]*0+a[1]*rp[b[0]]+b[1])%m)
# [x,y]*[u,v] = [x+u, y*r^u+v]
def mul(a,b): return ((a[0]+b[0])%n,(a[1]*rp[b[0]]+b[1])%m)
e=(0,0)
def inverse(a):
    u=(-a[0])%n; v=(-a[1]*rp[u])%m   # [x,y]*[u',v'] = [0, y*r^u' + v'] -> v' = -y r^u'
    g=(u,v); assert mul(a,g)==e and mul(g,a)==e; return g
gens=[]
for a in S: gens+=[a,inverse(a)]
for a in inv_l:
    a=(int(a[0]),int(a[1])); assert inverse(a)==a; gens.append(a)
assert len(set(gens))==len(gens) and e not in gens
deg=len(gens)
dist={e:0}; fr=[e]; layers=[1]
for k in range(1,D+2):
    nf=[]
    for x in fr:
        for g in gens:
            y=mul(x,g)   # right multiplication = Cayley graph (same graph up to iso as left)
            if y not in dist: dist[y]=k; nf.append(y)
    fr=nf
    if not nf: break
    layers.append(len(nf))
ecc=max(dist.values())
print(f"order={n*m} reached={len(dist)} degree={deg} ecc_from_identity={ecc} layers={layers}")
ok=len(dist)==n*m and deg==d and ecc<=D
print("VERIFIED_OK" if ok else "FAILED")
sys.exit(0 if ok else 1)
