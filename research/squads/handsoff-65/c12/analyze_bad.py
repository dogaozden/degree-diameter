import sys
from collections import deque, Counter
f = sys.argv[1]
L = open(f).read().split()
n = int(L[0]); E = [(int(L[i]), int(L[i+1])) for i in range(1, len(L), 2)]
adj = [[] for _ in range(n)]
for u, v in E:
    adj[u].append(v); adj[v].append(u)
# orbit sizes given as argv: A size then B sizes
sizes = [int(x) for x in sys.argv[2].split(',')]
bounds = []; s = 0
for z in sizes:
    bounds.append((s, s + z)); s += z
def orb(v):
    for i, (a, b) in enumerate(bounds):
        if a <= v < b: return i
bad = Counter(); tot = 0
for s0 in range(n):
    d = [-1] * n; d[s0] = 0; q = deque([s0])
    while q:
        x = q.popleft()
        for y in adj[x]:
            if d[y] < 0: d[y] = d[x] + 1; q.append(y)
    for t in range(s0 + 1, n):
        if d[t] < 0 or d[t] > 5:
            bad[(orb(s0), orb(t))] += 1; tot += 1
print("bad unordered pairs", tot)
for k, c in sorted(bad.items()): print("orbit pair", k, c)
