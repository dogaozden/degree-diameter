# incidence graph of PG(2,4) as base for voltage lifts (card x1)
import itertools
def mul(a,b):
    a1,a0=a>>1,a&1; b1,b0=b>>1,b&1
    c1=(a1&b1)^(a1&b0)^(a0&b1); c0=(a1&b1)^(a0&b0)
    return (c1<<1)|c0
def dot(p,q):
    s=0
    for x,y in zip(p,q): s^=mul(x,y)
    return s
pts=[]
for v in itertools.product(range(4),repeat=3):
    if v==(0,0,0): continue
    first=[x for x in v if x][0]
    if first==1: pts.append(v)   # normalized: first nonzero coordinate = 1
assert len(pts)==21
edges=[(i,21+j) for i,p in enumerate(pts) for j,L in enumerate(pts) if dot(p,L)==0]
assert len(edges)==105, len(edges)
with open('pg24.base','w') as f:
    f.write(f"42 {len(edges)}\n")
    for u,v in edges: f.write(f"{u} {v}\n")
from collections import Counter
print('degrees', set(Counter([u for u,v in edges]).values()), set(Counter([v for u,v in edges]).values()))
