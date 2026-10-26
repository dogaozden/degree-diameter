# c10(ii) group scan: order-2 symmetric S={x,ax,y,ay}, a(t,j)=(-t,j), groups of order 1094..1110 (every metacyclic group, capped)
import sys
from gen import metas
from sym2 import run
res=[]
G=[g for g in metas(1094,1110) if g[1]>2]
for (N,m,k,r) in G[:60]:
    (c1,x1,y1),(c2,x2,y2),ne=run(N,m,k,r,1500,3)
    res.append((c2,N,m,k,r,x2,y2))
res.sort()
for row in res[:8]: print("cost=%d N=%d meta %d %d %d x=%d y=%d"%row)
print("groups:",len(G[:60]),"best",res[0])
