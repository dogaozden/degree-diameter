import sys
from collections import deque, Counter
f, h = sys.argv[1], int(sys.argv[2])
L = open(f).read().split('\n'); n = int(L[0])
adj = [[] for _ in range(n)]
for s in L[1:]:
    if s.strip():
        a, b = map(int, s.split()); adj[a].append(b); adj[b].append(a)
d = [-1] * n; d[h] = 0; q = deque([h])
while q:
    x = q.popleft()
    for y in adj[x]:
        if d[y] < 0: d[y] = d[x] + 1; q.append(y)
miss = [x for x in range(n) if d[x] > 7]
print('misses', len(miss), 'by level', Counter(x // 7812 if x < 23436 else ('LH' if x < 23517 else 'PH') for x in miss))
print('by distance', Counter(d[x] for x in miss), 'nbrs', adj[h])
print('nbr dists', [ (u, d[u]) for u in adj[h]][:3])
