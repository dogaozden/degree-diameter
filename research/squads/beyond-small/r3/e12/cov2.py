from collections import deque
H=16896; n=2*H
E='/home/user/degree-diameter/research/squads/beyond-small/data/d16D5_n33792.edges'
adj=[[] for _ in range(n)]
with open(E) as f:
    f.readline()
    for l in f:
        u,v=map(int,l.split()); adj[u].append(v); adj[v].append(u)
import sys
for line in list(open(sys.argv[1]))[:int(sys.argv[2])]:
    N=list(map(int,line.split()))
    side = 'A' if N[0]<H else 'B'
    dist={x:0 for x in N}; q=deque(N)
    while q:
        x=q.popleft()
        if dist[x]>=3: continue
        for y in adj[x]:
            if y not in dist: dist[y]=dist[x]+1; q.append(y)
    cnt=sum(1 for v in range(n) if v not in dist and ((v>=H)==(side=='A')))
    print(side, 'uncovered other-side:', cnt)
