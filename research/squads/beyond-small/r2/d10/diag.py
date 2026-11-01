import sys
from collections import deque
from collections import Counter
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
conn = list(range(nbase+nh, n))
# side of a vertex: parity of distance from vertex 0 (bipartite); hubs are A-side, old A 0..16895, old B 16896..
side = bfs(0)
for c in conn[:int(sys.argv[4])]:
    d = bfs(c)
    bad = Counter()
    for v in range(n):
        if d[v] < 0: bad['unreach'] += 1
        elif (d[v] > 4 if side[v] % 2 == side[c] % 2 else d[v] > 5): bad[('same' if side[v]%2==side[c]%2 else 'opp', d[v])] += 1
    print('connector', c, 'deg', len(adj[c]), 'bad', dict(bad))
