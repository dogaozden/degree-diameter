import sys
from collections import Counter
fn = sys.argv[1]
with open(fn) as f:
    N = int(f.readline())
    adj = [[] for _ in range(N)]
    for line in f:
        u, v = map(int, line.split())
        adj[u].append(v); adj[v].append(u)
print('N', N, 'degree counts', Counter(len(a) for a in adj))
half = N // 2
def unreached(src):
    dist = {src: 0}; fr = [src]
    for d in range(5):
        nf = []
        for v in fr:
            for u in adj[v]:
                if u not in dist:
                    dist[u] = d + 1; nf.append(u)
        fr = nf
    return N - len(dist)
tot = 0
for s in [0, 1, 255, half, half + 1]:
    print('source', s, 'unreached', unreached(s))
