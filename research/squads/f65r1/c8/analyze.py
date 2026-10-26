import sys, collections
from collections import deque
f=open('/home/user/degree-diameter/research/fresh65/seeds/d6D5_n630_A3_2_chambers.edges').read().split()
n=int(f[0]); E=[(int(f[i]),int(f[i+1])) for i in range(1,len(f),2)]
adj=[[] for _ in range(n)]
for u,v in E: adj[u].append(v); adj[v].append(u)
print("n",n,"m",len(E),"deg set",set(len(a) for a in adj))
# bipartition
col=[-1]*n; col[0]=0; q=deque([0])
while q:
    u=q.popleft()
    for v in adj[u]:
        if col[v]<0: col[v]=1-col[u]; q.append(v)
print("sides",collections.Counter(col))
def bfs(s):
    d=[-1]*n; d[s]=0; q=deque([s])
    while q:
        u=q.popleft()
        for v in adj[u]:
            if d[v]<0: d[v]=d[u]+1; q.append(v)
    return d
D=[bfs(s) for s in range(n)]
print("diam",max(max(r) for r in D))
hist=collections.Counter()
for s in range(n):
    for t in range(s+1,n):
        if col[s]==col[t]: hist[D[s][t]]+=1
print("same-side dist hist (unordered pairs)",sorted(hist.items()))
# per-vertex same side count at dist>4 (should be 0) and number at dist 4
cnt4=[sum(1 for t in range(n) if col[t]==col[s] and t!=s and D[s][t]==4) for s in range(n)]
print("dist4 per vertex",collections.Counter(cnt4))
# edge removability: remove edge, check diameter (cheap: count bad same-side pairs)
def bad_pairs(adjx):
    tot=0
    for s in range(n):
        d=[-1]*n; d[s]=0; q=deque([s])
        while q:
            u=q.popleft()
            for v in adjx[u]:
                if d[v]<0: d[v]=d[u]+1; q.append(v)
        for t in range(n):
            if col[t]==col[s] and t!=s and (d[t]<0 or d[t]>4): tot+=1
    return tot//2
import pickle
# check edge types: 2-regular subgraph test via common neighbour structure
# count triangles-like: 4-cycles through each edge
c4=collections.Counter()
for u,v in E:
    cc=0
    for w in adj[u]:
        if w==v: continue
        for x in adj[w]:
            if x!=u and v in adj[x]: cc+=1
    c4[cc]+=1
print("4-cycles per edge(paths of len3 closing)", c4)
