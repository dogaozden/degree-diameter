import sys, collections
def load(fn):
    with open(fn) as f:
        toks = f.read().split()
    n = int(toks[0]); E = []
    for i in range(1, len(toks), 2):
        E.append((int(toks[i]), int(toks[i+1])))
    adj = [[] for _ in range(n)]
    for u, v in E:
        adj[u].append(v); adj[v].append(u)
    return n, E, adj
def bfs(adj, s):
    n = len(adj); d = [-1]*n; d[s] = 0; q = [s]
    for x in q:
        for y in adj[x]:
            if d[y] < 0:
                d[y] = d[x]+1; q.append(y)
    return d
if __name__ == "__main__":
    n, E, adj = load(sys.argv[1])
    print("n", n, "edges", len(E), "deg", collections.Counter(len(a) for a in adj))
    far = []
    per = [0]*n
    dist_hist = collections.Counter()
    for s in range(n):
        d = bfs(adj, s)
        for t in range(s+1, n):
            dd = d[t] if d[t] >= 0 else 99
            dist_hist[dd] += 1
            if dd > 5:
                far.append((s, t, dd)); per[s] += 1; per[t] += 1
    print("far pairs", len(far), "dist hist", sorted(dist_hist.items())[:12])
    print("per-vertex far count hist", sorted(collections.Counter(per).items()))
    print("far dists", collections.Counter(d for _,_,d in far))
    print("far pairs sample", far[:12])
