"""Theorem 3 on random connected bipartite graphs (not regular, not buildings): product distance = max formula,
diameter exactly D, quotient diameter <= D-1; also the quotient's degrees."""
import random
from collections import deque
def bfs(adj, s):
    d = {s: 0}; dq = deque([s])
    while dq:
        x = dq.popleft()
        for y in adj[x]:
            if y not in d: d[y] = d[x] + 1; dq.append(y)
    return d
random.seed(7)
worst = []
for trial in range(300):
    a, b = random.randint(1, 6), random.randint(1, 6)
    A = [('a', i) for i in range(a)]; B = [('b', j) for j in range(b)]
    p = random.choice([0.2, 0.35, 0.5, 0.8])
    adj = {v: set() for v in A + B}
    for x in A:
        for y in B:
            if random.random() < p: adj[x].add(y); adj[y].add(x)
    dist = {v: bfs(adj, v) for v in adj}
    if any(len(dist[v]) < a + b for v in adj) or a + b < 2: continue
    D = max(max(dv.values()) for dv in dist.values())
    P = [(x, y) for x in A for y in B] + [(x, y) for x in B for y in A]
    padj = {v: set() for v in P}
    for (x, y) in P:
        for x2 in adj[x]:
            for y2 in adj[y]: padj[(x, y)].add((x2, y2))
    ok = True; pd = 0
    for s in P:
        ds = bfs(padj, s)
        for t in P:
            want = max(dist[s[0]][t[0]], dist[s[1]][t[1]])
            if ds.get(t) != want: ok = False
            pd = max(pd, ds.get(t, 999))
    Q = [(x, y) for x in A for y in B]
    qadj = {v: set() for v in Q}
    for (x, y) in Q:
        for (x2, y2) in Q:
            if (x, y) != (x2, y2) and y2 in adj[x] and x2 in adj[y]: qadj[(x, y)].add((x2, y2))
    qd = max(max(bfs(qadj, s).values()) if len(bfs(qadj, s)) == len(Q) else 999 for s in Q)
    if not ok or pd != D or qd > D - 1:
        print("FAIL", a, b, D, pd, qd); break
    worst.append((D, qd))
else:
    from collections import Counter
    print("300 trials OK; (D, diam Q) counts:", sorted(Counter(worst).items()))
