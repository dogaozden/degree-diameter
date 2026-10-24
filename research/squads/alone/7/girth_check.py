"""Count 4-cycles (and check girth >= 6) of an edge list: python3 girth_check.py EDGES.
A 4-cycle exists iff some vertex u and vertex y != u share >= 2 neighbours."""
import sys
from collections import Counter

with open(sys.argv[1]) as f:
    n = int(f.readline())
    adj = [[] for _ in range(n)]
    for line in f:
        a, b = map(int, line.split())
        adj[a].append(b)
        adj[b].append(a)

bad_pairs = 0       # ordered (u, y) with >= 2 common neighbours
max_common = 0
hist = Counter()
for u in range(n):
    cnt = Counter()
    for x in adj[u]:
        for y in adj[x]:
            if y != u:
                cnt[y] += 1
    for y, c in cnt.items():
        hist[c] += 1
        max_common = max(max_common, c)
        if c >= 2:
            bad_pairs += 1
print(f"n={n} max_degree={max(map(len, adj))} min_degree={min(map(len, adj))}")
print(f"ordered pairs (u,y) at distance-2 with c common nbrs: {dict(sorted(hist.items()))}")
print(f"max common neighbours = {max_common}; ordered pairs with >=2 common = {bad_pairs}")
print("girth >= 6 (no 4-cycles)" if bad_pairs == 0 else "4-cycles present")
