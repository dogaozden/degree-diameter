import sys
from collections import deque
def load(p):
    L = open(p).read().split('\n')
    b, E = map(int, L[0].split())
    adj = [[] for _ in range(b)]
    for line in L[2:2+E]:
        a, c = map(int, line.split()[:2]); adj[a].append(c); adj[c].append(a)
    return b, adj
def diam(b, adj):
    worst = 0; hist = {}
    for s in range(b):
        d = [-1]*b; d[s] = 0; q = deque([s])
        while q:
            x = q.popleft()
            for y in adj[x]:
                if d[y] < 0: d[y] = d[x]+1; q.append(y)
        worst = max(worst, max(d))
        for v in range(b):
            if d[v] > 5: hist[d[v]] = hist.get(d[v], 0) + 1
    return worst, hist
for p in sys.argv[1:]:
    b, adj = load(p)
    w, h = diam(b, adj)
    print(p, 'base vertices', b, 'base diameter', w, 'pairs with dist>5 (ordered, by dist):', h)
