# usage: analyze.py EDGES -> counts far pairs by side type, and per-vertex unreached distribution
import sys
from collections import deque
L = open(sys.argv[1]).read().split()
n = int(L[0]); adj = [[] for _ in range(n)]
for i in range(1, len(L), 2):
    a, b = int(L[i]), int(L[i+1]); adj[a].append(b); adj[b].append(a)
col = [-1]*n; col[0] = 0; q = deque([0])
while q:
    x = q.popleft()
    for y in adj[x]:
        if col[y] < 0: col[y] = 1 - col[x]; q.append(y)
same = opp = 0; per = []
for s in range(n):
    d = [-1]*n; d[s] = 0; q = deque([s])
    while q:
        x = q.popleft()
        for y in adj[x]:
            if d[y] < 0: d[y] = d[x] + 1; q.append(y)
    far = [t for t in range(n) if t != s and (d[t] < 0 or d[t] > 7)]
    per.append(len(far))
    for t in far:
        if t > s:
            if col[t] == col[s]: same += 1
            else: opp += 1
print("far pairs same-side", same, "opposite-side", opp, "total", same + opp)
print("vertices with far>0:", sum(1 for x in per if x), "max per vertex", max(per))
