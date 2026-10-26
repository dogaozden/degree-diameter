"""Independent check: cubic, bipartite, same-side distance <= 4, every vertex on a 4-cycle. usage: bfs_check.py FILE"""
import sys
from collections import deque
lines = open(sys.argv[1]).read().split()
n = int(lines[0]); m = n // 2
E = [(int(lines[i]), int(lines[i+1])) for i in range(1, len(lines), 2)]
adj = [set() for _ in range(n)]
for u, v in E:
    assert (u < m) != (v < m), 'not bipartite across A/B'
    adj[u].add(v); adj[v].add(u)
assert all(len(adj[v]) == 3 for v in range(n)), 'not cubic'
def dist(s):
    d = {s: 0}; q = deque([s])
    while q:
        x = q.popleft()
        for y in adj[x]:
            if y not in d:
                d[y] = d[x] + 1; q.append(y)
    return d
ok_dist = True
for s in range(n):
    d = dist(s)
    for t in range(n):
        if (s < m) == (t < m) and t != s and d.get(t, 99) > 4:
            ok_dist = False
ok_c4 = all(any(len(adj[x] & adj[y]) >= 2 for x in adj[v] for y in adj[v] if x < y) for v in range(n))
print(f'n={n} m={m} cubic=True bipartite=True same_side_dist<=4={ok_dist} every_vertex_on_C4={ok_c4} VALID={ok_dist and ok_c4}')
