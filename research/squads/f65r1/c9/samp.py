import sys, random
sys.argv += []
from collections import deque
def load(p):
    with open(p) as f:
        n = int(f.readline()); M = [list(map(int, f.readline().split())) for _ in range(n)]
    return n, M
def cost(n, M, S):
    NV=2*n; adj=[[] for _ in range(NV)]
    for x in range(n):
        for s in S:
            y=M[s][x]; adj[x].append(n+y); adj[n+y].append(x)
    bad=0
    for v in range(NV):
        dist=[-1]*NV; dist[v]=0; q=deque([v])
        while q:
            u=q.popleft()
            for w in adj[u]:
                if dist[w]<0: dist[w]=dist[u]+1; q.append(w)
        side = range(n) if v<n else range(n,NV)
        bad += sum(1 for w in side if dist[w]<0 or dist[w]>4)
    return bad
n, M = load(sys.argv[1])
random.seed(1)
vals=[]
for _ in range(8):
    S=random.sample(range(n),6); vals.append(cost(n,M,S))
print(sorted(vals))
