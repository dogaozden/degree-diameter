# independent check: count ordered pairs at distance > D (unreachable counts), and the diameter, by plain BFS
import sys
from collections import deque
fn, D = sys.argv[1], int(sys.argv[2])
lines = open(fn).read().split()
n = int(lines[0])
adj = [[] for _ in range(n)]
for k in range(1, len(lines), 2):
    a, b = int(lines[k]), int(lines[k + 1])
    adj[a].append(b)
    adj[b].append(a)
far = 0
diam = 0
for s in range(n):
    dist = [-1] * n
    dist[s] = 0
    q = deque([s])
    while q:
        x = q.popleft()
        for y in adj[x]:
            if dist[y] < 0:
                dist[y] = dist[x] + 1
                q.append(y)
    for t in range(n):
        if dist[t] < 0 or dist[t] > D:
            far += 1
        if dist[t] > diam:
            diam = dist[t]
print(f'n={n} degs={set(len(a) for a in adj)} ordered_pairs_far(>{D})={far} maxdist_seen={diam}')
