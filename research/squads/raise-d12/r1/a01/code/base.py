# Base graph: incidence graph of H(2) (Tutte 12-cage), read from hexgen2 output. Checks girth, diameter, and
# counts nonbacktracking walks of length <= 12 between base vertices (upper bound on lift group order m).
import struct, sys
from collections import deque
F = '/home/user/degree-diameter/research/squads/raise-d12/r1/a01/hex/hex_q2.bin'
b = open(F, 'rb').read()
q, N, L = struct.unpack('<iii', b[:12])
pts = struct.unpack('<%di' % (L * (q + 1)), b[12:12 + 4 * L * (q + 1)])
n = N + L  # points 0..N-1, lines N..N+L-1
adj = [[] for _ in range(n)]
for l in range(L):
    for k in range(q + 1):
        p = pts[l * (q + 1) + k]
        adj[p].append(N + l); adj[N + l].append(p)
E = sum(len(a) for a in adj) // 2
print('n', n, 'edges', E, 'degrees', set(len(a) for a in adj))
def bfs(s):
    d = [-1] * n; d[s] = 0; dq = deque([s])
    while dq:
        x = dq.popleft()
        for y in adj[x]:
            if d[y] < 0: d[y] = d[x] + 1; dq.append(y)
    return d
diam = max(max(bfs(s)) for s in range(n))
print('diameter', diam)
# girth: min over edges of shortest cycle through the edge
g = 10**9
for s in range(n):
    d = [-1]*n; par = [-1]*n; d[s]=0; dq=deque([s])
    while dq:
        x = dq.popleft()
        for y in adj[x]:
            if d[y] < 0: d[y]=d[x]+1; par[y]=x; dq.append(y)
            elif par[x] != y: g = min(g, d[x]+d[y]+1)
print('girth', g)
# nonbacktracking walks of length <= 12 from u, counted by endpoint (dynamic programming on (vertex, last edge))
MAXL = 12
def walk_counts(u):
    # cnt[v] = number of nonbacktracking walks u->v of length <= MAXL (length 0 included for v=u)
    cnt = [0]*n
    cur = {(u, -1): 1}   # state (current vertex, previous vertex)
    cnt[u] += 1
    for step in range(MAXL):
        nxt = {}
        for (x, p), c in cur.items():
            for y in adj[x]:
                if y == p: continue
                nxt[(y, x)] = nxt.get((y, x), 0) + c
        for (y, x), c in nxt.items():
            cnt[y] += c
        cur = nxt
    return cnt
W = [walk_counts(u) for u in range(n)]
minW_adj = min(W[u][v] for u in range(n) for v in adj[u])
print('min over adjacent ordered pairs of #nb walks length<=12:', minW_adj)
print('min over all pairs of #nb walks length<=12:', min(W[u][v] for u in range(n) for v in range(n)))
from collections import Counter
print('histogram of adjacent-pair counts:', sorted(Counter(W[u][v] for u in range(n) for v in adj[u]).items()))
print('histogram of point->all counts (points):', sorted(Counter(W[0][v] for v in range(n)).items()))
