import sys, random
sys.path.insert(0, ".")
from exp import cost
from collections import deque
def haar_diam(S, n):
    # vertices: ('A',x), ('B',x); A x ~ B (x+s)
    N = 2*n; adj = [[] for _ in range(N)]
    for x in range(n):
        for s in S:
            y = (x+s) % n
            adj[x].append(n+y); adj[n+y].append(x)
    worst = 0
    for src in range(N):
        dist = [-1]*N; dist[src] = 0; q = deque([src])
        while q:
            u = q.popleft()
            for v in adj[u]:
                if dist[v] < 0:
                    dist[v] = dist[u]+1; q.append(v)
        if min(dist) < 0: return 10**9
        worst = max(worst, max(dist))
    return worst
random.seed(1)
agree = 0; tot = 0; sols = 0
for trial in range(300):
    n = random.choice([40, 60, 80, 100]); d = random.choice([3,4,5])
    S = random.sample(range(n), d)
    dm = haar_diam(S, n) <= 8
    c = cost(S, n) == 0
    tot += 1; agree += (dm == c); sols += dm
print("agree", agree, "of", tot, "diam<=8 count", sols)
