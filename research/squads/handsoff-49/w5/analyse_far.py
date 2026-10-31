"""Which lift vertices are unreached from the base roots within D=9? Usage: analyse_far.py EDGES N H"""
import sys, collections
from collections import deque
path, N, H = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
lines = open(path).read().split("\n")
n = int(lines[0]); adj = [[] for _ in range(n)]
for ln in lines[1:]:
    if not ln.strip(): continue
    u, v = map(int, ln.split()); adj[u].append(v); adj[v].append(u)
def ball(root):
    dist = [-1] * n; dist[root] = 0; q = deque([root])
    while q:
        x = q.popleft()
        if dist[x] >= 9: continue
        for y in adj[x]:
            if dist[y] < 0: dist[y] = dist[x] + 1; q.append(y)
    return dist
far = []
for u in range(H):
    d = ball(u * N)  # root = (u, identity)
    for w in range(H):
        for x in range(N):
            if d[w * N + x] < 0: far.append((u, w, x))
print("unreached (root, v, x):", len(far))
print("by root:", collections.Counter(f[0] for f in far))
print("by (root,v):", collections.Counter((f[0], f[1]) for f in far).most_common(6))
print("sample:", far[:12])
