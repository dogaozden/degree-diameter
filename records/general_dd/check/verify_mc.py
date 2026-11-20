#!/usr/bin/env python3
"""Independent check of a Cayley graph of G=Z_m x|_r Z_n (elements [x,y], x in Z_n, y in Z_m,
[x,y]*[u,v]=[x+u, y*r^u+v]); right-multiplication Cayley graph, numpy BFS from identity.
usage: verify_mc.py m n r D u1 v1 u2 v2 ... [inv u v]   -> prints order, degree, eccentricity, layer sizes; exit 0 iff diameter<=D
Checks: r^n=1 mod m, generators/inverses distinct & non-identity, group law closure by construction."""
import sys, numpy as np
a=sys.argv[1:]; m,n,r,D=map(int,a[:4]); rest=a[4:]
gens=[];i=0
while i<len(rest):
    if rest[i]=='inv': gens.append((int(rest[i+1])%n,int(rest[i+2])%m,True)); i+=3
    else: gens.append((int(rest[i])%n,int(rest[i+1])%m,False)); i+=2
assert pow(r,n,m)==1%m, "r^n != 1"
rp=[pow(r,k,m) for k in range(n)]
def mul(g,h): return ((g[0]+h[0])%n, (g[1]*rp[h[0]]+h[1])%m)
def inv(g):
    x=(-g[0])%n; return (x,(-g[1]*pow(rp[x],1,m))%m)   # [x,y]^-1 = [-x, -y r^{-x}]
S=set()
for u,v,isinv in gens:
    g=(u,v); gi=inv(g)
    assert mul(g,gi)==(0,0), "inverse wrong"
    if isinv: assert g==gi, "not an involution"
    assert g!=(0,0), "identity generator"
    S.add(g); S.add(gi)
S=sorted(S); deg=len(S)
N=n*m
du=np.array([g[0] for g in S],dtype=np.int64); dv=np.array([g[1] for g in S],dtype=np.int64)
rpa=np.array(rp,dtype=np.int64)
seen=np.zeros(N,dtype=bool); seen[0]=True
fr=np.array([0],dtype=np.int64); layers=[1]
for t in range(1,D+1):
    x=fr//m; y=fr%m
    nx=[];
    for k in range(deg):
        x2=(x+du[k])%n; y2=(y*rpa[du[k]]+dv[k])%m
        nx.append(x2*m+y2)
    c=np.unique(np.concatenate(nx)); c=c[~seen[c]]; seen[c]=True; fr=c; layers.append(len(c))
    if len(c)==0: break
ok=bool(seen.all())
print(f"order={N} degree={deg} D={D} covered={int(seen.sum())} layers={layers} {'OK' if ok else 'FAIL'}")
sys.exit(0 if ok else 1)
