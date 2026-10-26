import sys
from collections import deque
fn=sys.argv[1]; nlev=int(sys.argv[2]); K=int(sys.argv[3])   # nlev = 2*N*M level vertices; hubs are nlev..nlev+2K-1
f=open(fn); n=int(f.readline())
adj=[[] for _ in range(n)]
for line in f:
    a,b=map(int,line.split()); adj[a].append(b); adj[b].append(a)
def bfs(s):
    d=[-1]*n; d[s]=0; dq=deque([s])
    while dq:
        u=dq.popleft()
        for w in adj[u]:
            if d[w]<0: d[w]=d[u]+1; dq.append(w)
    return d
bad_hubs=0; worst=0; bad_lev=0; examples=[]
Bh=range(nlev,nlev+K); Ah=range(nlev+K,nlev+2*K)
for s in list(Bh)+list(Ah):
    d=bfs(s)
    for t in range(nlev,n):
        if d[t]>6 and (t-nlev<K)==(s<nlev+K):
            bad_hubs+=1
            if len(examples)<3: examples.append((s,t,d[t]))
    m=max(d); worst=max(worst,m)
print("hub-hub same colour pairs with dist>6:", bad_hubs, "examples", examples)
print("max eccentricity from hubs:", worst)
# sample level vertices
import random
random.seed(1)
cnt=0; mx=0
for s in random.sample(range(nlev),40):
    d=bfs(s)
    mx=max(mx,max(d))
    cnt+=sum(1 for x in d if x>7)
print("sampled level sources: max ecc", mx, "pairs >7 among sampled:", cnt)
