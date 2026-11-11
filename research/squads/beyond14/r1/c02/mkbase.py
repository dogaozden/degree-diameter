# Build cubic bases from LCF notation, verify girth and bipartiteness, write bipartite-relabelled edge file.
import sys, collections
def lcf_graph(L, reps):
    m = len(L) * reps
    adj = [set() for _ in range(m)]
    for i in range(m):
        adj[i].add((i + 1) % m); adj[(i + 1) % m].add(i)
    for i in range(m):
        j = (i + L[i % len(L)]) % m
        adj[i].add(j); adj[j].add(i)
    return adj
def girth(adj):
    best = 10**9
    n = len(adj)
    for s in range(n):
        dist = {s: 0}; par = {s: -1}; q = collections.deque([s])
        while q:
            x = q.popleft()
            for y in adj[x]:
                if y not in dist:
                    dist[y] = dist[x] + 1; par[y] = x; q.append(y)
                elif par[x] != y:
                    best = min(best, dist[x] + dist[y] + 1)
    return best
def bipart(adj):
    col = [-1] * len(adj); col[0] = 0; q = collections.deque([0]); ok = True
    while q:
        x = q.popleft()
        for y in adj[x]:
            if col[y] < 0: col[y] = 1 - col[x]; q.append(y)
            elif col[y] == col[x]: ok = False
    return ok, col
def write(adj, col, fn):
    A = [v for v in range(len(adj)) if col[v] == 0]; B = [v for v in range(len(adj)) if col[v] == 1]
    idx = {v: i for i, v in enumerate(A)}; idx.update({v: len(A) + i for i, v in enumerate(B)})
    edges = sorted({(idx[u], idx[v]) for u in range(len(adj)) for v in adj[u] if col[u] == 0})
    assert all(len(adj[v]) == 3 for v in range(len(adj)))
    with open(fn, 'w') as f:
        f.write(f"{len(adj)}\n")
        for u, v in edges: f.write(f"{u} {v}\n")
    return len(adj), len(edges)
specs = {
 'tutte12': ([17,27,-13,-59,-35,35,-11,13,-53,53,-27,21,57,11,-21,-57,59,-17], 7),
 'foster90': ([17,-9,37,-37,9,-17], 15),
 'tutte8': ([-13,-9,7,-7,9,13], 5),
}
out = sys.argv[1]
for name, (L, r) in specs.items():
    adj = lcf_graph(L, r)
    g = girth(adj); ok, col = bipartite_ok = bipart(adj)
    print(name, 'v=', len(adj), 'girth=', g, 'bipartite=', ok, 'deg3=', all(len(a)==3 for a in adj))
    if ok:
        print(' wrote', write(adj, col, f"{out}/{name}.txt"))
