#!/usr/bin/env python3
"""independent_bfs.py WITNESSFILE : low-memory pure-python check of a finalize.py witness file (group Z_m x|_r Z_n, [x,y][u,v]=[x+u,y*r^u+v]).
Checks r^n=1 mod m, generators distinct/non-identity, closure under inverses, BFS from identity (bytearray visited) covers all n*m with eccentricity <= D, degree.
Right-multiplication Cayley graph; vertex-transitive so eccentricity of identity = diameter."""
import sys,re
t=open(sys.argv[1]).read(); h=dict(re.findall(r'(\w+)=(\d+)',t.split('\n')[0]))
d,D,N,m,n,r=[int(h[k]) for k in ('d','D','N','m','n','r')]
S=[(int(a),int(b)) for a,b in re.findall(r'\((\d+),(\d+)\)',t.split('set:')[1])]
inv_l=re.findall(r'inv\((\d+),(\d+)\)',t)
assert N==n*m and pow(r,n,m)==1%m
rp=[pow(r,k,m) for k in range(n)]
def mul(a,b): return ((a[0]+b[0])%n,(a[1]*rp[b[0]]+b[1])%m)
e=(0,0)
def inverse(a):
    u=(-a[0])%n; v=(-a[1]*rp[u])%m
    g=(u,v); assert mul(a,g)==e and mul(g,a)==e; return g
gens=[]
for a in S: gens+=[a,inverse(a)]
for a in inv_l:
    a=(int(a[0]),int(a[1])); assert inverse(a)==a; gens.append(a)
assert len(set(gens))==len(gens) and e not in gens
deg=len(gens)
vis=bytearray(N); vis[0]=1; from array import array
fr=array("Q",[0]); layers=[1]; total=1
for k in range(1,D+2):
    nf=array("Q")
    for code in fr:
        x,y=divmod(code,m)
        for u,v in gens:
            c=((x+u)%n)*m+(y*rp[u]+v)%m
            if not vis[c]: vis[c]=1; nf.append(c)
    fr=nf
    if not nf: break
    layers.append(len(nf)); total+=len(nf)
ecc=len(layers)-1
print(f"order={n*m} reached={total} degree={deg} ecc_from_identity={ecc} layers={layers}")
ok=total==n*m and deg==d and ecc<=D
print("VERIFIED_OK" if ok else "FAILED")
sys.exit(0 if ok else 1)
