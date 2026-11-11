import sys
from collections import deque
fn, nbase, nh = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
lines = open(fn).read().split('\n'); n = int(lines[0])
adj = [[] for _ in range(n)]
for l in lines[1:]:
    if l.strip():
        u, v = map(int, l.split()); adj[u].append(v); adj[v].append(u)
def bfs(s):
    d = [-1]*n; d[s] = 0; q = deque([s])
    while q:
        x = q.popleft()
        for y in adj[x]:
            if d[y] < 0: d[y] = d[x]+1; q.append(y)
    return d
conns = list(range(nbase+nh, n))
from collections import Counter
cnt = Counter()
for c in conns[:20]:
    d = bfs(c)
    for c2 in conns:
        if c2 != c: cnt[d[c2]] += 1
print('connector-to-connector distance histogram (first 20 connectors as sources):', dict(cnt))
