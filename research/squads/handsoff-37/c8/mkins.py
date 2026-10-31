# Insert one A-B pair into a cubic bipartite edge list: delete x1y1, x2y2 (x in A, y in B); add a~y1,y2,b and b~x1,x2,a.
# usage: mkins.py IN OUT SEED   (picks random edge pairs with distinct endpoints)
import sys, random
src, dst, seed = sys.argv[1], sys.argv[2], int(sys.argv[3])
random.seed(seed)
L = open(src).read().split()
n = int(L[0]); E = [(int(L[i]), int(L[i+1])) for i in range(1, len(L), 2)]
# orientation: A = smaller colour class from BFS
adj = {v: [] for v in range(n)}
for a, b in E: adj[a].append(b); adj[b].append(a)
col = {0: 0}; q = [0]
for x in q:
    for y in adj[x]:
        if y not in col: col[y] = 1 - col[x]; q.append(y)
E = [(a, b) if col[a] == 0 else (b, a) for a, b in E]
while True:
    (x1, y1), (x2, y2) = random.sample(E, 2)
    if x1 != x2 and y1 != y2 and (x1, y2) not in E and (x2, y1) not in E:
        break
A = n // 2; B0 = n // 2
# relabel: new a = n (A side index A), new b = n+1 (B side); keep old labels; output as edge list with n+2 vertices
a, b = n, n + 1
newE = [e for e in E if e not in ((x1, y1), (x2, y2))]
newE += [(x1, b), (x2, b), (a, y1), (a, y2), (a, b)]
with open(dst, 'w') as f:
    f.write(f"{n+2}\n")
    for u, v in newE: f.write(f"{u} {v}\n")
print("inserted", len(newE), "edges, n", n + 2)
