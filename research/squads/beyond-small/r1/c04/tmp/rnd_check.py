import random
N = 2*69*256//2   # per side
random.seed(1)
n = 69*256
adj = [[] for _ in range(2*n)]
for _ in range(17):
    p = list(range(n)); random.shuffle(p)
    for a in range(n):
        adj[a].append(n + p[a]); adj[n + p[a]].append(a)
def unreached(src):
    dist = {src: 0}; fr = [src]
    for d in range(5):
        nf = []
        for v in fr:
            for u in adj[v]:
                if u not in dist:
                    dist[u] = d + 1; nf.append(u)
        fr = nf
    return 2*n - len(dist)
print('random 17-regular bipartite, N=', 2*n, 'unreached from A0:', unreached(0), 'from B0:', unreached(n))
