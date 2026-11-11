"""w17: BFS level sizes from the A-root (vertex 0) and a B-root of an edge-list file: python3 levels.py FILE"""
import sys
from collections import deque
def load(path):
    with open(path) as f:
        n = int(f.readline())
        adj = [[] for _ in range(n)]
        for line in f:
            p = line.split()
            if len(p) == 2:
                u, v = int(p[0]), int(p[1]); adj[u].append(v); adj[v].append(u)
    return n, adj
def levels(adj, root, maxd=10):
    dist = {root: 0}; q = deque([root]); cnt = [0] * (maxd + 1); cnt[0] = 1
    while q:
        v = q.popleft()
        if dist[v] >= maxd: continue
        for w in adj[v]:
            if w not in dist:
                dist[w] = dist[v] + 1; cnt[dist[w]] += 1; q.append(w)
    return cnt
if __name__ == "__main__":
  n, adj = load(sys.argv[1])
  N = n // 2
  for name, root in (("A-root", 0), ("B-root", N)):
      c = levels(adj, root)
      print(name, "level sizes d=0..10:", c, "cum<=8:", sum(c[:9]), "cum<=9:", sum(c[:10]))
