# insert one more vertex pair into an existing bipartite 6-regular graph (edge list), 5 matching edges removed
# usage: stack.py IN OUT SEED
import sys, random
from collections import deque
random.seed(int(sys.argv[3]))
L = open(sys.argv[1]).read().split()
n = int(L[0]); E = [(int(L[1 + 2 * i]), int(L[2 + 2 * i])) for i in range((len(L) - 1) // 2)]
adj = [[] for _ in range(n)]
for a, b in E: adj[a].append(b); adj[b].append(a)
side = [-1] * n; side[0] = 0; q = deque([0])
while q:
    x = q.popleft()
    for y in adj[x]:
        if side[y] < 0: side[y] = 1 - side[x]; q.append(y)
A = [(a, b) if side[a] == 0 else (b, a) for a, b in E]
while True:
    random.shuffle(A)
    ch = []; ua = set(); ub = set()
    for a, b in A:
        if a in ua or b in ub: continue
        ch.append((a, b)); ua.add(a); ub.add(b)
        if len(ch) == 5: break
    if len(ch) == 5: break
rem = set(ch)
F = [e for e in A if e not in rem]
u, v = n, n + 1
for a, b in ch: F.append((u, b)); F.append((a, v))
F.append((u, v))
N = n + 2
deg = [0] * N
for a, b in F: deg[a] += 1; deg[b] += 1
assert all(d == 6 for d in deg)
with open(sys.argv[2], 'w') as f:
    f.write(f"{N}\n")
    for a, b in F: f.write(f"{a} {b}\n")
print("n", N, "edges", len(F))
