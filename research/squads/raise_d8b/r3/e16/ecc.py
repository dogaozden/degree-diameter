import sys
from collections import deque
f = sys.argv[1]; hubs = list(map(int, sys.argv[2].split(',')))
L = open(f).read().split('\n'); n = int(L[0])
adj = [[] for _ in range(n)]
for s in L[1:]:
    if s.strip():
        a, b = map(int, s.split()); adj[a].append(b); adj[b].append(a)
for h in hubs:
    d = [-1] * n; d[h] = 0; q = deque([h])
    while q:
        x = q.popleft()
        for y in adj[x]:
            if d[y] < 0: d[y] = d[x] + 1; q.append(y)
    far = sum(1 for x in d if x > 7)
    print('hub', h, 'deg', len(adj[h]), 'ecc', max(d), 'vertices at distance > 7:', far)
