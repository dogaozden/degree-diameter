# r2d/farpairs.py EDGES [SIGMA]: list far pairs (dist > 7) and per-vertex far counts; Moore-tree excess per vertex.
import sys
from collections import deque, Counter
toks = open(sys.argv[1]).read().split(); n = int(toks[0])
N = [[] for _ in range(n)]
for i in range(1, len(toks), 2):
    a, b = int(toks[i]), int(toks[i+1]); N[a].append(b); N[b].append(a)
m = n // 2
D = []
for s in range(n):
    d = [-1]*n; d[s] = 0; q = deque([s])
    while q:
        x = q.popleft()
        for y in N[x]:
            if d[y] < 0: d[y] = d[x]+1; q.append(y)
    D.append(d)
far = [(u, v) for u in range(n) for v in range(u+1, n) if D[u][v] > 7]
print('far', len(far))
cnt = Counter(); [cnt.update([u, v]) for u, v in far]
print('vertices involved', len(cnt), 'max per vertex', cnt.most_common(8))
print('distance histogram of far pairs', Counter(D[u][v] for u, v in far))
# Moore excess: walks of even length <= 6 from A-vertex v, collisions
def excess(v):
    side = 0 if v < m else 1
    cur = {(v, -1): 1}; reached = set([v]); total = 1
    # NB walks of length <= 6 ending at even distance
    frontier = [(v, -1)]
    for L in range(1, 7):
        nf = []
        for (x, p) in frontier:
            for y in N[x]:
                if y != p: nf.append((y, x))
        frontier = nf
        if L % 2 == 0:
            for (x, p) in frontier: reached.add(x); total += 1
    same = sum(1 for x in reached if (x < m) == (v < m))
    return total - same  # excess walks (collisions) among same-side endpoints
ex = [excess(v) for v in range(n)]
print('excess walks per vertex: min', min(ex), 'max', max(ex), 'hist', sorted(Counter(ex).items()))
