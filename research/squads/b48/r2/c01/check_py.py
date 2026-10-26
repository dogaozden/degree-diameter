# validation: far counts from (e,A) and (e,B) by BFS on the Haar graph, compared with the C walk counter
import sys, random
import numpy as np
tab, S = sys.argv[1], [int(x) for x in sys.argv[2:6]]
with open(tab, "rb") as f:
    N = int(np.fromfile(f, dtype=np.int32, count=1)[0])
    T = np.fromfile(f, dtype=np.uint16, count=N * N).reshape(N, N)
adj = [[] for _ in range(2 * N)]
for s in S:
    for g in range(N):
        a, b = g, N + int(T[s, g])
        adj[a].append(b); adj[b].append(a)
far = 0
for src in (0, N):
    dist = [-1] * (2 * N); dist[src] = 0; q = [src]
    for v in q:
        for w in adj[v]:
            if dist[w] < 0:
                dist[w] = dist[v] + 1; q.append(w)
    far += sum(1 for d in dist if d > 8 or d < 0)
print("py_far", far)
