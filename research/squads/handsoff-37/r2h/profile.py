# sorted multiset of (side, eccentricity-ish) profile: per vertex, histogram of BFS distance counts
import sys, collections
from collections import deque
def load(p):
    f = open(p); n = int(f.readline()); adj = [[] for _ in range(n)]
    for line in f:
        a, b = map(int, line.split()); adj[a].append(b); adj[b].append(a)
    return n, adj
def prof(n, adj):
    out = []
    for s in range(n):
        dist = [-1]*n; dist[s] = 0; q = deque([s])
        while q:
            x = q.popleft()
            for y in adj[x]:
                if dist[y] < 0: dist[y] = dist[x]+1; q.append(y)
        c = collections.Counter(dist)
        out.append((len(adj[s]), tuple(sorted(c.items()))))
    return sorted(out)
a = prof(*load(sys.argv[1])); b = prof(*load(sys.argv[2]))
print('identical distance profiles' if a == b else 'profiles differ')
