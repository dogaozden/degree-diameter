import sys, collections
from collections import deque
def load(fn):
    L=open(fn).read().split(); n=int(L[0]); E=[(int(L[i]),int(L[i+1])) for i in range(1,len(L),2)]
    adj=[[] for _ in range(n)]
    for a,b in E: adj[a].append(b); adj[b].append(a)
    return n,adj
def bfs(adj,s):
    d=[-1]*len(adj); d[s]=0; q=deque([s])
    while q:
        x=q.popleft()
        for y in adj[x]:
            if d[y]<0: d[y]=d[x]+1; q.append(y)
    return d
n,adj=load(sys.argv[1])
# side by BFS
side=bfs(adj,0); side=[x%2 for x in side]
far=[]
D=[bfs(adj,s) for s in range(n)]
for s in range(n):
    for t in range(s+1,n):
        if D[s][t]>7 or D[s][t]<0: far.append((s,t,D[s][t]))
print("far pairs",len(far))
print("dist histogram", collections.Counter(d for _,_,d in far))
print("same-side", sum(1 for s,t,d in far if side[s]==side[t]), "opp", sum(1 for s,t,d in far if side[s]!=side[t]))
deg=collections.Counter()
for s,t,d in far: deg[s]+=1; deg[t]+=1
print("bad vertices", len(deg), "degree hist", collections.Counter(deg.values()))
