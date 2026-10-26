"""D(4,16): size of the same-side 4-ball from a point and from a line (needs >= half of a side for an involution
quotient to have diameter 5)."""
import numpy as np, sys
from collections import deque
import lu_graphs as lu
k, q = int(sys.argv[1]), int(sys.argv[2])
n, adj = lu.build(k, q)
def balls(s):
    N = len(adj); d = np.full(N, -1, dtype=np.int64); d[s] = 0; dq = deque([s])
    while dq:
        u = dq.popleft()
        if d[u] >= 6: continue
        for w in adj[u]:
            if d[w] < 0: d[w] = d[u] + 1; dq.append(w)
    side = slice(0, n) if s < n else slice(n, 2 * n)
    dd = d[side]
    return {r: int(((dd >= 0) & (dd <= r)).sum()) for r in (2, 4, 6)}
print(f'D({k},{q}): side {n}; ball sizes from a point', balls(0), 'from a line', balls(n))
