import sys
from collections import deque
def load(fn):
    with open(fn) as f:
        n=int(f.readline()); adj=[[] for _ in range(n)]
        for line in f:
            p=line.split()
            if len(p)<2: continue
            u,v=int(p[0]),int(p[1]); adj[u].append(v); adj[v].append(u)
    return n,adj
def bfs(adj,s):
    d=[-1]*len(adj); d[s]=0; q=deque([s])
    while q:
        u=q.popleft()
        for w in adj[u]:
            if d[w]<0: d[w]=d[u]+1; q.append(w)
    return d
if __name__=="__main__":
    n,adj=load(sys.argv[1]); N=n//2
    for s in [0,N]:
        d=bfs(adj,s)
        far=[v for v in range(n) if d[v]>8 or d[v]<0]
        print("src",s,"far",len(far),[ (v//N, v%N, d[v]) for v in far])
