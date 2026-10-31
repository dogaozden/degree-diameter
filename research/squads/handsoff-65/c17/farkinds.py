import sys
from collections import deque, Counter
# usage: farkinds.py EDGES ORBIT_SIZES(comma list, vertex blocks in order)
# prints far unordered pairs (distance > 5) counted by the pair of orbit blocks they lie in
fn = sys.argv[1]
sizes = [int(x) for x in sys.argv[2].split(',')]
with open(fn) as f:
    n = int(f.readline())
    adj = [[] for _ in range(n)]
    for line in f:
        p = line.split()
        if len(p) == 2:
            u, v = int(p[0]), int(p[1])
            adj[u].append(v); adj[v].append(u)
blk = []
for i, s in enumerate(sizes):
    blk += [i] * s
assert len(blk) == n
cnt = Counter()
far_total = 0
for s in range(n):
    dist = [-1] * n
    dist[s] = 0
    q = deque([s])
    while q:
        v = q.popleft()
        if dist[v] == 5:
            continue
        for w in adj[v]:
            if dist[w] < 0:
                dist[w] = dist[v] + 1
                q.append(w)
    for t in range(s + 1, n):
        if dist[t] < 0:
            far_total += 1
            cnt[(blk[s], blk[t])] += 1
print("far unordered pairs", far_total)
for k in sorted(cnt):
    print("blocks", k, "pairs", cnt[k])
