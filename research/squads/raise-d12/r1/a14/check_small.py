# independent check: explicit Haar graph on SL(2,8) x Z_p, plain BFS, for the S printed by orb7
import sys, itertools
from collections import deque
def gf(a,b):
    r=0
    for i in range(3):
        if (b>>i)&1: r^=a<<i
    for i in (4,3):
        if (r>>i)&1: r^=0b1011<<(i-3)
    return r
def mm(X,Y):
    a1,b1,c1,d1=X; a2,b2,c2,d2=Y
    return (gf(a1,a2)^gf(b1,c2), gf(a1,b2)^gf(b1,d2), gf(c1,a2)^gf(d1,c2), gf(c1,b2)^gf(d1,d2))
p=int(sys.argv[1]); S=[]
for line in open(sys.argv[2]):
    if line.startswith('S '):
        _,M,z=line.split(); S.append((int(M),int(z)))
# decode matrix index M as in orb7.c: enumeration order a,b,c,d over 0..7 with det 1
mats=[]
for a in range(8):
  for b in range(8):
    for c in range(8):
      for d in range(8):
        if gf(a,d)^gf(b,c)==1: mats.append((a,b,c,d))
Sg=[(mats[M],z) for M,z in S]
def gm(x,y): return (mm(x[0],y[0]),(x[1]+y[1])%p)
e=((1,0,0,1),0)
def inv(x):
    a,b,c,d=x[0]; return ((d,b,c,a),(-x[1])%p)  # inverse in SL(2,8) is adjugate (char 2 signs trivial)
# sanity: inv check
for x in Sg[:2]:
    assert gm(x,inv(x))==e
Sinv=[inv(s) for s in Sg]
# BFS on Haar graph: A-vertices g, B-vertices g; edge (g,A)-(s g,B)
dist={}
start=('A',e); dist[start]=0; q=deque([start])
while q:
    side,g=q.popleft(); d=dist[(side,g)]
    if side=='A':
        nbrs=[('B',gm(s,g)) for s in Sg]
    else:
        nbrs=[('A',gm(s,g)) for s in Sinv]  # g' with s g' = h  -> g' = s^-1 h
    for v in nbrs:
        if v not in dist:
            dist[v]=d+1; q.append(v)
for lev in range(1,13):
    cB=sum(1 for (sd,g),d in dist.items() if sd=='B' and d<=lev)
    cA=sum(1 for (sd,g),d in dist.items() if sd=='A' and d<=lev)
    if lev in (1,2,3,4,5,6,7,8,9,10,11,12):
        print('LEV',lev,'cumB',cB,'cumA',cA)
