import sys
from collections import deque
def load(fn):
    with open(fn) as f:
        n = int(f.readline())
        adj = [[] for _ in range(n)]
        for line in f:
            p = line.split()
            if len(p) < 2: continue
            u, v = int(p[0]), int(p[1])
            adj[u].append(v); adj[v].append(u)
    return n, adj
def cost(n, adj):
    # same-side pairs at distance > 4 (ordered), plus unreachable
    bad = 0; maxdeg = max(len(a) for a in adj)
    col = [-1]*n; col[0] = 0; q0 = deque([0])
    while q0:
        u = q0.popleft()
        for w in adj[u]:
            if col[w] < 0: col[w] = 1-col[u]; q0.append(w)
    for s in range(n):
        dist = [-1]*n; dist[s] = 0; q = deque([s])
        while q:
            u = q.popleft()
            if dist[u] >= 5: continue
            for w in adj[u]:
                if dist[w] < 0:
                    dist[w] = dist[u]+1; q.append(w)
        for t in range(n):
            if col[t] == col[s] and t != s and (dist[t] < 0 or dist[t] > 4):
                bad += 1
    return bad, maxdeg
if __name__ == "__main__":
    n, adj = load(sys.argv[1])
    print(cost(n, adj))
