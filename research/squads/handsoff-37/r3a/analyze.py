import sys, collections
from collections import deque
f = sys.argv[1]
L = open(f).read().split('\n')
n = int(L[0]); adj = [[] for _ in range(n)]
for line in L[1:]:
    if line.strip():
        a, b = map(int, line.split()); adj[a].append(b); adj[b].append(a)
side = [0 if v < n // 2 else 1 for v in range(n)]
# side: check bipartition via BFS from 0
col = [-1] * n; col[0] = 0; dq = deque([0])
while dq:
    x = dq.popleft()
    for y in adj[x]:
        if col[y] < 0: col[y] = 1 - col[x]; dq.append(y)
side = col
far = []
dist_all = []
for s in range(n):
    d = [-1] * n; d[s] = 0; dq = deque([s])
    while dq:
        x = dq.popleft()
        for y in adj[x]:
            if d[y] < 0: d[y] = d[x] + 1; dq.append(y)
    dist_all.append(d)
    for t in range(s + 1, n):
        if d[t] > 7 or d[t] < 0: far.append((s, t, d[t]))
print('far pairs', len(far), 'distance hist', collections.Counter(x[2] for x in far))
print('same side', sum(1 for s, t, _ in far if side[s] == side[t]), 'cross', sum(1 for s, t, _ in far if side[s] != side[t]))
deg = collections.Counter()
for s, t, _ in far: deg[s] += 1; deg[t] += 1
print('vertices in far pairs', len(deg), 'max per vertex', max(deg.values()), 'hist', collections.Counter(deg.values()))
print('girth-ish: count of 4-cycles', sum(1 for x in range(n) for y in adj[x] for z in adj[y] if z != x for w in adj[z] if w != y and x in adj[w] and x != z) // 8)
