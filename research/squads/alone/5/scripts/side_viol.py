# for a source, list violating targets (dist > 5 or unreachable) split by side (A: id < nA, B: id >= nA)
import sys
from graph import load
from collections import deque
path, s = sys.argv[1], int(sys.argv[2])
n, adj, E = load(path); nA = 15730
d = [-1] * n; d[s] = 0; q = deque([s])
while q:
    x = q.popleft()
    for y in adj[x]:
        if d[y] < 0: d[y] = d[x] + 1; q.append(y)
def side(v): return 'A' if v < nA else 'B'
bad = {}
for v in range(n):
    if d[v] < 0 or d[v] > 5:
        key = (side(v), d[v]); bad[key] = bad.get(key, 0) + 1
print('source', s, 'side', side(s), 'violations by (side,dist):', bad)
