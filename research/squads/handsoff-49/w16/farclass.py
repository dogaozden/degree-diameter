"""w16: for a lift edge list (vertex (u,x) = u*N + x, N = 71*7, x = a + 71 t), BFS from each base root (u,0) and tabulate
the far vertices by their abelianisation class t (x // 71) and by the base vertex side. Usage: farclass.py EDGES B N"""
import sys
from collections import deque, Counter
f, B, N = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
ls = open(f).read().split("\n")
n = int(ls[0]); adj = [[] for _ in range(n)]
for l in ls[1:]:
    if l.strip():
        u, v = map(int, l.split()); adj[u].append(v); adj[v].append(u)
tot = Counter(); per_root = []
for r in range(B):
    s = r * N
    dist = [-1] * n; dist[s] = 0; q = deque([s])
    while q:
        x = q.popleft()
        for y in adj[x]:
            if dist[y] < 0: dist[y] = dist[x] + 1; q.append(y)
    far = [v for v in range(n) if dist[v] < 0 or dist[v] > 9]
    per_root.append(len(far))
    for v in far: tot[(v // N, (v % N) // 71)] += 1
print("far per root:", per_root)
print("far by (base vertex, t = abelianisation class):", sorted(tot.items())[:40])
