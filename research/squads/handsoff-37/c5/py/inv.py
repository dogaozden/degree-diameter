import sys
from collections import deque, Counter
def load(p):
    t = open(p).read().split(); n = int(t[0]); N = [[] for _ in range(n)]
    for i in range(1, len(t), 2):
        a, b = int(t[i]), int(t[i+1]); N[a].append(b); N[b].append(a)
    return n, N
def inv(p):
    n, N = load(p); m = n // 2
    fc = []; allfar = 0
    D = []
    for s in range(n):
        d = [-1]*n; d[s] = 0; q = deque([s])
        while q:
            x = q.popleft()
            for y in N[x]:
                if d[y] < 0: d[y] = d[x]+1; q.append(y)
        D.append(d)
        fc.append(sum(1 for t in range(n) if d[t] > 7 or d[t] < 0))
    # number of 4-cycles and 6-cycles through vertex 0 type stats: count of pairs at distance 2 with multiple common nbrs
    c4 = 0
    for a in range(n):
        for b in range(a+1, n):
            k = len(set(N[a]) & set(N[b]))
            if k >= 2: c4 += k*(k-1)//2
    dist_hist = Counter(D[0])
    return sum(fc)//2, c4, tuple(sorted(Counter(fc).items())), tuple(sorted(dist_hist.items()))
for p in sys.argv[1:]:
    print(p, inv(p))
