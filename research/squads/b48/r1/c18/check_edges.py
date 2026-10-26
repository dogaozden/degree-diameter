import sys
from collections import deque
f = sys.argv[1]
lines = open(f).read().split('\n')
n = int(lines[0]); adj = [[] for _ in range(n)]
for ln in lines[1:]:
    if not ln.strip(): continue
    u, v = map(int, ln.split()); adj[u].append(v); adj[v].append(u)
N = n // 4
def ecc_far(s):
    d = [-1]*n; d[s] = 0; q = deque([s])
    while q:
        x = q.popleft()
        for y in adj[x]:
            if d[y] < 0: d[y] = d[x] + 1; q.append(y)
    return sum(1 for z in range(n) if d[z] < 0 or d[z] > 8), max(d)
for u in range(4):
    print("root", u*N, "far>8:", ecc_far(u*N))
