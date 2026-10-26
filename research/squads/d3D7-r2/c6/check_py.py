import sys
from collections import deque
q,a,b,c,d = map(int, sys.argv[1:6])
n=2*q
adj=[set() for _ in range(n)]
def add(u,v): adj[u].add(v); adj[v].add(u)
for x in range(q):
    add(x,q+x); add(x,q+(a*x+b)%q); add(x,q+(c*x+d)%q)
bad=0
for s in range(n):
    dist=[-1]*n; dist[s]=0; dq=deque([s])
    while dq:
        u=dq.popleft()
        for v in adj[u]:
            if dist[v]<0: dist[v]=dist[u]+1; dq.append(v)
    bad+=sum(1 for t in range(n) if dist[t]<0 or dist[t]>7)
print("py cost", bad, "max deg", max(len(s) for s in adj), "degs<3:", sum(1 for s in adj if len(s)<3))
