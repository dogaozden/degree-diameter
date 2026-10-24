# c7: coverage of a virtual hub h attached to chosen old vertices of the base graph (no edges removed).
# Counts old targets at distance > 7 from h, by (level, point/line). Reads the edge list written by lvl.c.
import sys, random
from collections import deque
N = 3906
def load(fn):
    with open(fn) as f:
        n = int(f.readline()); adj = [[] for _ in range(n)]
        for line in f:
            u, v = map(int, line.split()); adj[u].append(v); adj[v].append(u)
    return n, adj
def cls(v):
    i, r = divmod(v, 2 * N)
    return (i, 'P' if r < N else 'L')
def run(n, adj, nbrs_of_hub, label):
    adj2 = [list(a) for a in adj] + [list(nbrs_of_hub)]
    h = n
    for u in nbrs_of_hub: adj2[u].append(h)
    dist = [-1] * (n + 1); dist[h] = 0; dq = deque([h])
    while dq:
        v = dq.popleft()
        for w in adj2[v]:
            if dist[w] < 0: dist[w] = dist[v] + 1; dq.append(w)
    bad = {}; worst = 0
    for v in range(n):
        d = dist[v]; worst = max(worst, d)
        if d > 7 or d < 0: bad[cls(v)] = bad.get(cls(v), 0) + 1
    print(label, 'max dist =', worst, ' old targets at dist>7:', sum(bad.values()), dict(sorted(bad.items())))
n, adj = load(sys.argv[1])
rng = random.Random(7)
def pt(level): return level * 2 * N + rng.randrange(N)
for t in range(2):
    run(n, adj, [pt(0), pt(1), pt(2)], 'hub, 3 point nbrs (levels 0,1,2):')
for t in range(2):
    run(n, adj, [pt(0), pt(1)], 'hub, 2 point nbrs (levels 0,1):')
run(n, adj, [pt(0)], 'hub, 1 point nbr (level 0):')
