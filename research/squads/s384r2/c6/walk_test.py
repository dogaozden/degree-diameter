#!/usr/bin/env python3
"""Walk-count test on the base graph GQ(5,5) incidence graph.

A lift vertex (w,h) is within distance 5 of (v,0) iff some non-backtracking walk
R from v to w of length <= 5 has voltage h (any walk reduces freely to a
non-backtracking one with the same voltage and endpoint). So the number of
distinct NB walks of length <= 5 from v to w is the number of lift vertices over w
that can possibly be reached. Also counts NB closed walks (girth test).
"""
import sys
from collections import Counter

sys.setrecursionlimit(10000)
f = open("/home/user/degree-diameter/research/squads/s384r2/c6/gq55_edges.txt")
n, m = map(int, f.readline().split())
adj = [[] for _ in range(n)]
for _ in range(m):
    a, b = map(int, f.readline().split())
    adj[a].append(b)
    adj[b].append(a)


def nb_walks(v, L):
    """Count NB walks of length exactly L from v, grouped by endpoint."""
    out = Counter()

    def rec(x, prev, k):
        if k == L:
            out[x] += 1
            return
        for y in adj[x]:
            if y != prev:
                rec(y, x, k + 1)

    rec(v, -1, 0)
    return out


# dist-class statistics from source 0 (vertex-transitive on each side, checked below)
v = 0
by_len = {L: nb_walks(v, L) for L in range(1, 6)}
# Reachable-by-length-<=5 NB walk counts per endpoint, split by distance class
from collections import deque
dist = [-1] * n
dist[v] = 0
dq = deque([v])
while dq:
    x = dq.popleft()
    for y in adj[x]:
        if dist[y] < 0:
            dist[y] = dist[x] + 1
            dq.append(y)

cnt = Counter()  # (distance, endpoint) -> number of NB walks of length <=5 with matching parity
for L in range(1, 6):
    for w, c in by_len[L].items():
        cnt[w] += c
stats = {}
for w in range(n):
    if w == v:
        continue
    stats.setdefault(dist[w], []).append(cnt[w])
for d in sorted(stats):
    vals = stats[d]
    print(f"base distance {d}: #targets={len(vals)} NB walks (len<=5, both parities) min={min(vals)} max={max(vals)}")

# closed NB walks at v of length 1..7 (girth test): must be 0 for girth 8
for L in range(1, 8):
    print(f"closed NB walks at v of length {L}: {nb_walks(v, L).get(v, 0)}")
# per-length matching parity: count NB walks of the right parity (same parity as dist)
for d in (1, 2, 3, 4):
    vals = []
    for w in range(n):
        if dist[w] == d:
            vals.append(sum(by_len[L].get(w, 0) for L in range(1, 6) if L % 2 == d % 2))
    print(f"distance {d}, right-parity NB walks of length<=5 to each target: min={min(vals)} max={max(vals)}")
