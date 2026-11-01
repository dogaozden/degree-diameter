import sys
from collections import deque
fn, base_n = sys.argv[1], 33792
lines = open(fn).read().split('\n'); n = int(lines[0])
adj = [[] for _ in range(n)]
for l in lines[1:]:
    if not l.strip(): continue
    u, v = map(int, l.split()); adj[u].append(v); adj[v].append(u)
hubs = list(range(base_n, n))
bad = []
for s in hubs[int(sys.argv[3]):int(sys.argv[2])]:
    dist = [-1]*n; dist[s] = 0; q = deque([s])
    while q:
        u = q.popleft()
        for w in adj[u]:
            if dist[w] < 0: dist[w] = dist[u]+1; q.append(w)
    far = [v for v in hubs if dist[v] > 5]
    for v in far: bad.append((s, v, dist[v]))
    fo = [v for v in range(n) if dist[v] > 5]
    if fo: print('source', s, 'vertices at dist>5:', len(fo), 'hub targets', len(far), 'examples', far[:5], fo[:5])
print('bad hub pairs', len(bad), bad[:10])
