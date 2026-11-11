import sys, itertools
sys.path.insert(0,'.')
from gf import diam
def haar(elems,mul,S):
    idx={g:i for i,g in enumerate(elems)}; n=len(elems)
    edges=[(idx[g],n+idx[mul(s,g)]) for g in elems for s in S]
    assert len(set(edges))==len(edges)
    return diam(2*n,edges)
def cyc(cs):
    f=list(range(4))
    for c in cs:
        for i in range(len(c)): f[c[i]]=c[(i+1)%len(c)]
    return tuple(f)
S4=list(itertools.permutations(range(4)))
comp=lambda f,h: tuple(f[h[i]] for i in range(4))
G1=[(f,x) for f in S4 for x in range(24)]
S1=[(cyc([]),0),(cyc([(0,1),(2,3)]),23),(cyc([(0,3,2)]),0),(cyc([(0,2)]),18),(cyc([(0,1,2,3)]),18),(cyc([(1,2,3)]),17),(cyc([(1,2)]),3)]
m1=lambda a,b:(comp(a[0],b[0]),(a[1]+b[1])%24)
m1op=lambda a,b:(comp(b[0],a[0]),(a[1]+b[1])%24)
print("(7,5) f.h:",haar(G1,m1,S1)); print("(7,5) h.f:",haar(G1,m1op,S1))
G2=[(a,b,c) for a in range(11) for b in range(11) for c in range(11)]
m2=lambda u,v:((u[0]+v[0])%11,(u[1]+v[1])%11,(u[2]+v[2]+u[0]*v[1])%11)
S2=[(0,0,0),(8,6,10),(7,9,3),(10,1,8),(4,4,5),(5,5,8),(6,5,4),(1,0,9),(6,10,8)]
print("(9,5):",haar(G2,m2,S2))
G3=[(x,y,z) for x in range(7) for y in range(6) for z in range(21)]
m3=lambda u,v:((u[0]+pow(3,u[1],7)*v[0])%7,(u[1]+v[1])%6,(u[2]+v[2])%21)
S3=[(0,0,0),(0,4,5),(6,3,18),(6,5,6),(2,4,1),(2,2,16),(4,5,12),(2,3,15)]
# check group axioms quickly (associativity sample)
import random
for _ in range(2000):
    a,b,c=random.choice(G3),random.choice(G3),random.choice(G3)
    assert m3(m3(a,b),c)==m3(a,m3(b,c))
print("(8,5):",haar(G3,m3,S3))
