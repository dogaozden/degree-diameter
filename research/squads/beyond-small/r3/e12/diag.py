import sys
from collections import deque
fn=sys.argv[1]; H=16896; n0=2*H
lines=open(fn).read().split('\n')
n=int(lines[0]); adj=[[] for _ in range(n)]
for l in lines[1:]:
    if not l.strip(): continue
    u,v=map(int,l.split()); adj[u].append(v); adj[v].append(u)
orbs=[list(map(int,l.split())) for l in open(sys.argv[2]) if l.strip()]
hubs=[]
def sh(w,t):
    off=0 if w<H else H; loc=w-off; blk,y=divmod(loc,256); j,h=divmod(blk,22)
    return off+(j*22+(h+t)%22)*256+y
for N in orbs:
    for t in range(22): hubs.append(n0+len(hubs))
# hub ids n0.. are assigned in order of orbs x t; we check a sample of hub ids for eccentricity>5 vs any vertex
srcs=[int(x) for x in sys.argv[3].split(',')]
for s in srcs:
    dist=[-1]*n; dist[s]=0; q=deque([s])
    while q:
        x=q.popleft()
        for y in adj[x]:
            if dist[y]<0: dist[y]=dist[x]+1; q.append(y)
    far=[v for v in range(n) if dist[v]>5 or dist[v]<0]
    print('src',s,'side', 'hubA' if (s>=n0 and s < n0+1) else '', 'max',max(dist),'far',len(far), far[:5])
