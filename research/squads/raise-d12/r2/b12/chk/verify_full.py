# independent full check: build the whole bipartite Haar graph H(G,S) (2N vertices), BFS from (e,A) and (e,B).
# Right multiplication by G is transitive on each side, so ecc over these two sources = diameter.
import sys
from collections import deque
def run(path):
    lines = open(path).read().split()
    m, k, r = int(lines[0]), int(lines[1]), int(lines[2])
    S = [int(v) for v in lines[4:]]
    pw = [pow(r, y, m) for y in range(k)]
    def elem(i): return (i // k, i % k)
    def idx(x, y): return (x % m) * k + (y % k)
    N = m * k
    def mul(a, b):
        ax, ay = elem(a); bx, by = elem(b)
        return idx(ax + pw[ay] * bx, ay + by)
    def inv(a):
        x, y = elem(a); yi = (-y) % k
        return idx(-pw[yi] * x, yi)
    # adjacency of the bipartite graph: node 2g = (g,A), 2g+1 = (g,B); (g,A) ~ (s g,B)
    adj = [[] for _ in range(2 * N)]
    for g in range(N):
        for s in S:
            h = mul(s, g)
            adj[2 * g].append(2 * h + 1)
            adj[2 * h + 1].append(2 * g)
    assert len(set(S)) == len(S)
    ecc = []
    for src in (0, 1):
        dist = [-1] * (2 * N); dist[src] = 0; q = deque([src])
        while q:
            u = q.popleft()
            for v in adj[u]:
                if dist[v] < 0:
                    dist[v] = dist[u] + 1; q.append(v)
        ecc.append((min(dist) if False else max(dist), sum(1 for d in dist if d < 0)))
    deg_ok = all(len(adj[u]) == len(S) for u in range(2 * N))
    print(path, 'N', N, 'S', S, 'ecc(eA), ecc(eB) (max dist, unreached):', ecc, 'regular', deg_ok,
          'diameter<=12:', all(e[0] <= 12 and e[1] == 0 for e in ecc))
for p in sys.argv[1:]:
    run(p)
