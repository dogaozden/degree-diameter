import sys, collections
sys.path.insert(0,'.')
from analyze import load, bfs
n,E,adj=load(sys.argv[1])
col=[-1]*n; col[0]=0; q=[0]
for x in q:
    for y in adj[x]:
        if col[y]<0: col[y]=1-col[x]; q.append(y)
deg=[len(a) for a in adj]
far=[]
for s in range(n):
    d=bfs(adj,s)
    for t in range(s+1,n):
        if d[t]<0 or d[t]>5: far.append((s,t,d[t]))
pv=collections.Counter()
for s,t,_ in far: pv[s]+=1; pv[t]+=1
print("n",n,"far",len(far),"same-side",sum(1 for s,t,_ in far if col[s]==col[t]),"dists",collections.Counter(x[2] for x in far))
print("deficient vertices (deg<6):",[(v,col[v],deg[v],pv[v]) for v in range(n) if deg[v]<6][:12])
print("far pairs touching deficient:", sum(1 for s,t,_ in far if deg[s]<6 or deg[t]<6))
print("far-count hist per vertex:", sorted(collections.Counter(pv[v] for v in range(n)).items())[:15])
print("sides", collections.Counter(col))
