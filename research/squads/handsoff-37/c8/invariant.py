# usage: invariant.py EDGES... : per graph, a sorted multiset of vertex distance profiles (cheap isomorphism invariant)
import sys
from collections import deque, Counter
def profile(path):
    L = open(path).read().split(); n = int(L[0]); adj = [[] for _ in range(n)]
    for i in range(1, len(L), 2):
        a, b = int(L[i]), int(L[i+1]); adj[a].append(b); adj[b].append(a)
    prof = []
    for s in range(n):
        d = [-1]*n; d[s] = 0; q = deque([s])
        while q:
            x = q.popleft()
            for y in adj[x]:
                if d[y] < 0: d[y] = d[x] + 1; q.append(y)
        c = Counter(d)
        prof.append(tuple(sorted(c.items())))
    girth_cnt = None
    return hash(tuple(sorted(Counter(prof).items()))), Counter(prof).most_common(1)[0][1], len(Counter(prof))
for p in sys.argv[1:]:
    h, top, k = profile(p)
    print(p, "distinct vertex-profile classes:", k, "hash:", h % 10**8)
