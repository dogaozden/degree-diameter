"""Histogram of the number of NB walks of length <= 4 between a source and same-side targets at distance 4 (and of
length <= 5 to opposite-side targets) in C(2,q), from flags.py's edge list."""
import sys, numpy as np
from collections import Counter
E = [tuple(map(int, l.split())) for l in open(sys.argv[1]).read().split('\n')[1:] if l.strip()]
n = int(open(sys.argv[1]).readline())
adj = [[] for _ in range(n)]
for a, b in E: adj[a].append(b); adj[b].append(a)
def walks(s, L):
    # NB walk counts by (vertex, prev) dynamic programming
    cur = {(w, s): 1 for w in adj[s]}
    tot = Counter(); dist = {s: 0}
    for w in adj[s]: tot[w] += 1
    for l in range(2, L + 1):
        nxt = Counter()
        for (v, p), c in cur.items():
            for w in adj[v]:
                if w != p: nxt[(w, v)] += c
        for (w, v), c in nxt.items(): tot[w] += c
        cur = nxt
    return tot
from collections import deque
s = 0
d = [-1] * n; d[s] = 0; dq = deque([s])
while dq:
    u = dq.popleft()
    for w in adj[u]:
        if d[w] < 0: d[w] = d[u] + 1; dq.append(w)
t4 = walks(s, 4)
h = Counter(t4[v] for v in range(n) if d[v] == 4)
print("distance-4 targets by #walks of length <= 4:", sorted(h.items()))
t5 = walks(s, 5)
h5 = Counter(t5[v] for v in range(n) if d[v] == 5)
print("distance-5 targets by #walks of length <= 5:", sorted(h5.items())[:12], '...')
