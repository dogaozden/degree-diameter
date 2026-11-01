# usage: complete170.py IN169 OUT170 : add vertex y (side of B) adjacent to the three degree-2 vertices of side A
import sys
t = open(sys.argv[1]).read().split(); n = int(t[0]); E = [(int(t[i]), int(t[i+1])) for i in range(1, len(t), 2)]
deg = [0]*n; adj = [[] for _ in range(n)]
for a, b in E: deg[a] += 1; deg[b] += 1; adj[a].append(b); adj[b].append(a)
col = [-1]*n; col[0] = 0; q = [0]
for u in q:
    for w in adj[u]:
        if col[w] < 0: col[w] = 1 - col[u]; q.append(w)
defi = [v for v in range(n) if deg[v] < 3]
print('deficient', [(v, deg[v], col[v]) for v in defi], file=sys.stderr)
y = n
E2 = E + [(v, y) for v in defi]
assert all(col[v] == col[defi[0]] for v in defi)
with open(sys.argv[2], 'w') as f:
    f.write(f"{n+1}\n")
    for a, b in E2: f.write(f"{a} {b}\n")
