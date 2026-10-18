"""Greedy repair: add edges between vertices of spare degree until the diameter is <= D.
repair(n, edges, side, Delta, D) -> edges or None."""
from collections import deque


def dist_matrix(n, adj):
    INF = 99; Dm = []
    for s in range(n):
        d = [INF] * n; d[s] = 0; dq = deque([s])
        while dq:
            u = dq.popleft()
            for w in adj[u]:
                if d[w] == INF: d[w] = d[u] + 1; dq.append(w)
        Dm.append(d)
    return Dm


def repair(n, edges, side, Delta, D, verbose=False, max_add=200):
    edges = [tuple(e) for e in edges]
    adj = [set() for _ in range(n)]
    for u, v in edges: adj[u].add(v); adj[v].add(u)
    for step in range(max_add):
        Dm = dist_matrix(n, adj)
        far = [(u, v) for u in range(n) for v in range(u + 1, n) if Dm[u][v] > D]
        if not far:
            return edges
        if verbose: print(f'  step {step}: {len(far)} far pairs', flush=True)
        slackP = [u for u in range(n) if side[u] == 0 and len(adj[u]) < Delta]
        slackL = [u for u in range(n) if side[u] == 1 and len(adj[u]) < Delta]
        best = (0, None)
        # only consider edges touching a far pair's neighbourhood: a within dist D-1 of some far endpoint
        ends = {x for p in far for x in p}
        for a in slackP:
            da = Dm[a]
            if not any(da[x] <= D - 1 for x in ends): continue
            for b in slackL:
                if b in adj[a]: continue
                db = Dm[b]; c = 0
                for u, v in far:
                    if da[u] + 1 + db[v] <= D or db[u] + 1 + da[v] <= D: c += 1
                if c > best[0]: best = (c, (a, b))
        if best[1] is None:
            if verbose: print('  stuck', flush=True)
            return None
        a, b = best[1]; adj[a].add(b); adj[b].add(a); edges.append((min(a, b), max(a, b)))
    return None
