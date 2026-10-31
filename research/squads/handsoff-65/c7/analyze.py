import sys
from collections import deque
f = open(sys.argv[1]); n = int(f.readline())
E = [tuple(map(int, l.split())) for l in f if l.strip()]
adj = [[] for _ in range(n)]
for a, b in E: adj[a].append(b); adj[b].append(a)
# base 684 graph ends: new vertices are 684 and 685
new = {684, 685}
ends = set()
for a, b in E:
    pass
far = []
for s in range(n):
    dist = [-1]*n; dist[s] = 0; q = deque([s])
    while q:
        x = q.popleft()
        if dist[x] >= 5: continue
        for y in adj[x]:
            if dist[y] < 0: dist[y] = dist[x]+1; q.append(y)
    for t in range(s+1, n):
        if dist[t] < 0: far.append((s, t))
print("far pairs", len(far))
inv = sum(1 for s, t in far if s in new or t in new)
print("involving new vertices 684/685:", inv)
cnt = {}
for s, t in far:
    cnt[s] = cnt.get(s, 0) + 1; cnt[t] = cnt.get(t, 0) + 1
top = sorted(cnt.items(), key=lambda x: -x[1])[:12]
print("top vertices (vertex:far count):", top)
print("vertices with far pairs:", len(cnt))
