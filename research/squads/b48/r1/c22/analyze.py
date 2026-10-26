# far-set analysis of a cyclic lift: for each root (u,0), far vertices (v,x) grouped by base vertex v and by x
import sys
from collections import deque, Counter
f, N = sys.argv[1], int(sys.argv[2])
lines = open(f).read().split('\n')
n = int(lines[0]); adj = [[] for _ in range(n)]
for ln in lines[1:]:
    if ln.strip():
        u, v = map(int, ln.split()); adj[u].append(v); adj[v].append(u)
b = n // N
tot = Counter(); xs = Counter()
for u in range(b):
    src = u * N
    dist = [-1] * n; dist[src] = 0; q = deque([src])
    while q:
        a = q.popleft()
        for c in adj[a]:
            if dist[c] < 0: dist[c] = dist[a] + 1; q.append(c)
    far = [w for w in range(n) if dist[w] > 8]
    print(f"root {u}: far={len(far)} by side-base-vertex", dict(Counter(w // N for w in far)), "max dist", max(dist))
    for w in far: tot[w // N] += 1; xs[(w % N - 0) % N] += 1
print("x-values of far vertices (over roots), top:", xs.most_common(12))
print("distinct x:", len(xs), "of N =", N)
