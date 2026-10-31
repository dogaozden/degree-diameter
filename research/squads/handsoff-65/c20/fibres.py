import sys, collections
sys.path.insert(0,'.')
from analyze import load, bfs
fn=sys.argv[1]; F=int(sys.argv[2])   # F = fibre size
n,E,adj=load(fn)
# sides by BFS colouring
col=[-1]*n; col[0]=0; q=[0]
for x in q:
    for y in adj[x]:
        if col[y]<0: col[y]=1-col[x]; q.append(y)
far=[]
for s in range(n):
    d=bfs(adj,s)
    for t in range(s+1,n):
        if d[t]<0 or d[t]>5: far.append((s,t,d[t]))
print("n",n,"far",len(far),"dists",collections.Counter(x[2] for x in far))
print("sides same-side far pairs:", sum(1 for s,t,_ in far if col[s]==col[t]), "cross:", sum(1 for s,t,_ in far if col[s]!=col[t]))
cnt=collections.Counter()
for s,t,_ in far:
    cnt[(s//F, t//F)]+=1
print("fibre pair counts (top):", cnt.most_common(12))
pv=collections.Counter()
for s,t,_ in far: pv[s]+=1; pv[t]+=1
print("vertices on far pairs:", len(pv), "hist of per-vertex far counts:", sorted(collections.Counter(pv.values()).items())[:10])
