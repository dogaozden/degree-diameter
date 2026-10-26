# usage: edges.py TABLE.bin OUT.edges s1 s2 s3 s4   (Cayley graph Cay(G,{s1..s4}) with s's inverse-closed)
import sys, numpy as np
with open(sys.argv[1],'rb') as f:
    N = int(np.frombuffer(f.read(4), dtype=np.int32)[0])
    T = np.frombuffer(f.read(), dtype=np.uint16).reshape(N, N).astype(np.int64)
S = [int(x) for x in sys.argv[3:7]]
inv = {s: int(np.where(T[s] == 0)[0][0]) for s in S}
assert all(inv[s] in S for s in S), 'S not inverse-closed'
edges = set()
g = np.arange(N)
lines = []
used = set()
for s in S:
    if inv[s] == s:
        for x in range(N):
            y = int(T[x, s]); u, v = min(x, y), max(x, y)
            if u != v: edges.add((u, v))
    elif s not in used and inv[s] not in used:
        used.add(s); used.add(inv[s])
        for x in range(N):
            y = int(T[x, s]); u, v = min(x, y), max(x, y); edges.add((u, v))
with open(sys.argv[2], 'w') as f:
    f.write(f"{N}\n")
    for u, v in sorted(edges): f.write(f"{u} {v}\n")
degs = np.zeros(N, int)
for u, v in edges: degs[u] += 1; degs[v] += 1
print('edges', len(edges), 'degree set', sorted(set(degs.tolist())))
