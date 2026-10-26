"""Independent check of an edge list (first line n, then 'u v' lines): simple, regular degree, bipartite, diameter,
by 64-source bit-parallel BFS in numpy.  usage: bitcheck.py edges"""
import sys, numpy as np
f = open(sys.argv[1]); n = int(f.readline())
E = np.loadtxt(f, dtype=np.int64).reshape(-1, 2)
assert E.min() >= 0 and E.max() < n
assert (E[:, 0] != E[:, 1]).all(), "loop"
key = np.minimum(E[:, 0], E[:, 1]) * n + np.maximum(E[:, 0], E[:, 1])
assert len(np.unique(key)) == len(E), "multi-edge"
deg = np.bincount(E.ravel(), minlength=n); d = int(deg[0]); assert (deg == d).all(), "not regular"
adj = [[] for _ in range(n)]
for u, v in E: adj[u].append(v); adj[v].append(u)
A = np.array(adj, dtype=np.int64)          # n x d
col = -np.ones(n, dtype=np.int64); col[0] = 0; st = [0]
while st:
    u = st.pop()
    for v in adj[u]:
        if col[v] < 0: col[v] = 1 - col[u]; st.append(v)
        else: assert col[v] != col[u], "not bipartite"
assert (col >= 0).all(), "disconnected"
diam = 0
for s0 in range(0, n, 64):
    k = min(64, n - s0)
    reach = np.zeros(n, dtype=np.uint64)
    reach[s0:s0 + k] = np.left_shift(np.uint64(1), np.arange(k, dtype=np.uint64))
    full = np.uint64((1 << k) - 1) if k < 64 else np.uint64(0xFFFFFFFFFFFFFFFF)
    r = 0
    while True:
        if (reach == full).all(): break
        r += 1
        nb = np.bitwise_or.reduce(reach[A], axis=1)
        reach = reach | nb
        assert r <= 20
    diam = max(diam, r)
print(f"n={n} edges={len(E)} degree={d} bipartite=yes sides={int((col==0).sum())},{int((col==1).sum())} diameter={diam}")
