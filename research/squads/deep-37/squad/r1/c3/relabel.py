"""relabel.py IN OUT: relabel a bipartite edge list so that side A (containing vertex 0's colour class complement...)
is 0..NA-1 and B is NA..n-1; A is the side with more vertices (or the side of vertex 0 if equal). Prints NA."""
import sys
from collections import deque
L = open(sys.argv[1]).read().split()
n = int(L[0]); E = [(int(L[i]), int(L[i+1])) for i in range(1, len(L), 2)]
adj = [[] for _ in range(n)]
for a, b in E: adj[a].append(b); adj[b].append(a)
col = [-1]*n; col[0] = 0; q = deque([0])
while q:
    x = q.popleft()
    for y in adj[x]:
        if col[y] < 0: col[y] = 1 - col[x]; q.append(y)
A = [v for v in range(n) if col[v] == 0]; B = [v for v in range(n) if col[v] == 1]
if len(A) < len(B):
    A, B = B, A
    # keep side 0 as the larger one
lab = {v: i for i, v in enumerate(A + B)}
with open(sys.argv[2], 'w') as f:
    f.write(f"{n}\n")
    for a, b in E:
        u, w = lab[a], lab[b]
        if u > w: u, w = w, u
        f.write(f"{u} {w}\n")
print(len(A), len(B))
