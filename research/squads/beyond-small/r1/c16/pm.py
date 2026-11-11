# usage: pm.py in.edges seed out_matching.txt  -- random perfect matching of a bipartite regular graph (Hopcroft-Karp style augment)
import sys, random
from collections import deque
inp, seed, outp = sys.argv[1], int(sys.argv[2]), sys.argv[3]
random.seed(seed)
f = open(inp); n = int(f.readline())
E = [tuple(map(int, l.split())) for l in f if l.strip()]
adj = [[] for _ in range(n)]
for u, v in E: adj[u].append(v); adj[v].append(u)
col = [-1]*n; col[0] = 0; dq = deque([0])
while dq:
    x = dq.popleft()
    for y in adj[x]:
        if col[y] < 0: col[y] = 1-col[x]; dq.append(y)
L = [v for v in range(n) if col[v] == 0]
for v in range(n): random.shuffle(adj[v])
mate = [-1]*n
def hk():
    while True:
        dist = {}
        q = deque()
        for u in L:
            if mate[u] < 0: dist[u] = 0; q.append(u)
        found = False
        while q:
            u = q.popleft()
            for w in adj[u]:
                m2 = mate[w]
                if m2 < 0: found = True
                elif m2 not in dist: dist[m2] = dist[u]+1; q.append(m2)
        if not found: return
        def dfs(u):
            for w in adj[u]:
                m2 = mate[w]
                if m2 < 0 or (m2 in dist and dist[m2] == dist[u]+1 and dfs(m2)):
                    mate[u] = w; mate[w] = u; return True
            dist[u] = -1
            return False
        for u in L:
            if mate[u] < 0: dfs(u)
hk()
assert all(mate[v] >= 0 for v in range(n)), "not perfect"
with open(outp, 'w') as g:
    for u in L: g.write(f"{u} {mate[u]}\n")
print("matching size", len(L))
