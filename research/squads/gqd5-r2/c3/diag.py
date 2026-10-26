import sys, json, collections
from setup_common import *
from levels import build, write_edges
from collections import deque
edges_file = sys.argv[1]
lines = open(edges_file).read().split('\n')
n = int(lines[0]); adj = [[] for _ in range(n)]
for ln in lines[1:]:
    if ln.strip():
        a, b = map(int, ln.split()); adj[a].append(b); adj[b].append(a)
per = 2 * N
def name(v):
    if v < 3 * per:
        j, r = divmod(v, per)
        kind = ('P' if r < N else 'L')
        idx = r if r < N else r - N
        typ = 'D' if j == 0 else 'H'
        return 'L%d%s%d' % (j, kind, idx)
    return 'hub%d' % (v - 3 * per)
bad = collections.Counter(); ex = []
for s in range(3 * per):
    dist = [-1] * n; dist[s] = 0; dq = deque([s])
    while dq:
        x = dq.popleft()
        for y in adj[x]:
            if dist[y] < 0: dist[y] = dist[x] + 1; dq.append(y)
    for t in range(3 * per):
        if dist[t] > 5 or dist[t] < 0:
            bad[(name(s)[:2], name(t)[:2], dist[t])] += 1
            if len(ex) < 12: ex.append((name(s), name(t), dist[t]))
print('bad ordered pairs by (level,level,dist):', dict(bad))
print('examples', ex)
