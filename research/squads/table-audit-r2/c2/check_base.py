import sys
from collections import deque
L = open(sys.argv[1]).read().split()
b, E = int(L[0]), int(L[1])
ed = [(int(L[2+2*i]), int(L[3+2*i])) for i in range(E)]
adj = [[] for _ in range(b)]
for u, w in ed: adj[u].append(w); adj[w].append(u)
col = [-1]*b; col[0] = 0; q = deque([0]); ok = True
while q:
    x = q.popleft()
    for y in adj[x]:
        if col[y] < 0: col[y] = 1-col[x]; q.append(y)
        elif col[y] == col[x]: ok = False
print(sys.argv[1], "b", b, "E", E, "cubic", all(len(a) == 3 for a in adj), "bipartite", ok and min(col) >= 0)
