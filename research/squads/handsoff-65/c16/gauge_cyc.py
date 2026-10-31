# usage: python3 -I gauge_cyc.py IN_SOL M OUT_SOL : gauge-normalise a vl-format solution over Z_M (additive voltages)
# so that a BFS spanning tree from base vertex 0 has voltage 0 (tabu requires this).
import sys
from collections import deque
inp, M, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
L = open(inp).read().split('\n')
b, E = map(int, L[0].split()[:2])
sides = list(map(int, L[1].split()[:b]))
edges = []
for line in L[2:]:
    p = line.split()
    if len(p) >= 3 and not line.startswith('#') and p[0].lstrip('-').isdigit():
        edges.append((int(p[0]), int(p[1]), int(p[2])))
adj = [[] for _ in range(b)]
for i, (u, w, a) in enumerate(edges):
    adj[u].append((w, a, 1)); adj[w].append((u, a, -1))
x = [None] * b; x[0] = 0; dq = deque([0])
while dq:
    v = dq.popleft()
    for (y, a, s) in adj[v]:
        if x[y] is None:
            # edge e=(u,w,a): new volt = a + x_w - x_u must be 0 on the tree
            u, w = (v, y) if s == 1 else (y, v)
            x[y] = (x[v] if False else 0)  # placeholder, fixed below
            dq.append(y)
# recompute properly: x_w = x_u - a for tree edges (u side0, w side1)
x = [None] * b; x[0] = 0; dq = deque([0])
while dq:
    v = dq.popleft()
    for (y, a, s) in adj[v]:
        if x[y] is None:
            if s == 1:   # v = u (side 0), y = w: x_w = x_u - a
                x[y] = (x[v] - a) % M
            else:        # v = w, y = u: x_u = x_w + a
                x[y] = (x[v] + a) % M
            dq.append(y)
with open(out, 'w') as f:
    f.write(f"{b} {len(edges)}\n")
    f.write(" ".join(map(str, sides)) + "\n")
    for (u, w, a) in edges:
        f.write(f"{u} {w} {(a + x[w] - x[u]) % M}\n")
print("gauged", out, "tree edges set to 0; spanning tree check:", all(x[i] is not None for i in range(b)))
