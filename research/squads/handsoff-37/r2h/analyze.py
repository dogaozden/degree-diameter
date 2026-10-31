# far-pair breakdown for an n=169 edge list: which vertex classes carry the far pairs (same-side pairs beyond 6)
import sys, collections
from collections import deque
f = open(sys.argv[1]); n = int(f.readline())
adj = [[] for _ in range(n)]
for line in f:
    a, b = map(int, line.split()); adj[a].append(b); adj[b].append(a)
NT = 127
def cls(v):
    if v == 0: return 'x'
    if v < NT:
        d = (v + 1).bit_length() - 1
        return 'tree_d%d' % d
    return 'outer'
col = {}
dist_all = []
cnt = collections.Counter(); pairs = 0
for s in range(n):
    dist = [-1] * n; dist[s] = 0; q = deque([s])
    while q:
        x = q.popleft()
        for y in adj[x]:
            if dist[y] < 0: dist[y] = dist[x] + 1; q.append(y)
    for t in range(s + 1, n):
        if dist[t] > 7 or dist[t] < 0:
            pairs += 1; cnt[(cls(s), cls(t))] += 1
print('far pairs (dist>7 or disconnected):', pairs)
for k, v in sorted(cnt.items(), key=lambda kv: -kv[1])[:12]:
    print(k, v)
deg = collections.Counter(len(adj[v]) for v in range(n)); print('degree histogram', dict(deg))
