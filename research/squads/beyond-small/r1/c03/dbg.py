from collections import deque
import sys
f=open('best_n33850.edges').read().split('\n')
n=int(f[0]); adj=[[] for _ in range(n)]
for l in f[1:]:
    if l.strip():
        u,v=map(int,l.split()); adj[u].append(v); adj[v].append(u)
def bfs(s):
    d=[-1]*n; d[s]=0; q=deque([s])
    while q:
        x=q.popleft()
        for y in adj[x]:
            if d[y]<0: d[y]=d[x]+1; q.append(y)
    return d
bad=[]
for h in range(33792,n):
    d=bfs(h)
    far=[v for v in range(n) if d[v]>5 or d[v]<0]
    if far: bad.append((h,len(far),far[:5],[d[v] for v in far[:5]]))
print('hubs with far vertices', len(bad))
for b in bad[:5]: print(b)
