import sys, collections
def load(fn):
    with open(fn) as f:
        n = int(f.readline())
        adj = [[] for _ in range(n)]
        for line in f:
            p = line.split()
            if len(p) == 2:
                u, v = int(p[0]), int(p[1]); adj[u].append(v); adj[v].append(u)
    return n, adj
def profile(n, adj):
    rows = []
    for s in range(n):
        dist = [-1]*n; dist[s] = 0; q = [s]; cnt = collections.Counter()
        for x in q:
            for y in adj[x]:
                if dist[y] < 0:
                    dist[y] = dist[x]+1; cnt[dist[y]] += 1; q.append(y)
        rows.append(tuple(sorted(cnt.items())))
    return collections.Counter(rows)
n1, a1 = load(sys.argv[1]); n2, a2 = load(sys.argv[2])
p1 = profile(n1, a1); p2 = profile(n2, a2)
print("same vertex-profile multiset:", p1 == p2, "distinct profiles", len(p1), len(p2))
print("profile sample:", list(p1.items())[:2])
