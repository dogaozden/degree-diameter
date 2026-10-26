import sys, numpy as np
from collections import deque
sys.path.insert(0, "/home/user/degree-diameter/research/squads/b48/tools")
import groups
spec, volts = sys.argv[1], [int(x) for x in sys.argv[2:]]
T = groups.table(spec); N = len(T)
inv = [int(np.where(T[g] == 0)[0][0]) for g in range(N)]
# dipole: edges (0,1,g) for each volt g; lift vertex (v,x) = v*N+x; (0,x)~(1,x*g)
adj = [[] for _ in range(2 * N)]
for g in volts:
    for x in range(N):
        a, b = x, N + int(T[x, g])
        adj[a].append(b); adj[b].append(a)
def far(root):
    d = [-1] * (2 * N); d[root] = 0; q = deque([root])
    while q:
        u = q.popleft()
        for w in adj[u]:
            if d[w] < 0: d[w] = d[u] + 1; q.append(w)
    return sum(1 for v in range(2 * N) if d[v] < 0 or d[v] > 8)
print("cost", far(0) + far(N), "| ecc from (0,e) ball size", 2*N-far(0))
