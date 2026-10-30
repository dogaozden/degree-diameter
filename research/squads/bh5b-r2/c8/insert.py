# insert.py SRC.edges OUT.edges SEED K : add one A-vertex and one B-vertex to a 5-regular bipartite graph
# by removing K edges (a_i,b_i) with distinct endpoints, joining a' to all b_i and b' to all a_i.
import sys, random
src, out, seed, K = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
random.seed(seed)
L = open(src).read().split()
n = int(L[0]); E = [(int(L[i]), int(L[i+1])) for i in range(1, len(L), 2)]
adj = [[] for _ in range(n)]
for u, v in E: adj[u].append(v); adj[v].append(u)
col = [-1]*n; col[0] = 0; st = [0]
while st:
    x = st.pop()
    for y in adj[x]:
        if col[y] < 0: col[y] = 1-col[x]; st.append(y)
A = [v for v in range(n) if col[v] == 0]; B = [v for v in range(n) if col[v] == 1]
while True:
    rem = random.sample(E, K)
    if len({a for a, b in rem}) == K and len({b for a, b in rem}) == K: break
# rem edges (u,v) with u in A (colour 0 since edge list u<v and u in A? normalise)
rem2 = []
for u, v in rem:
    if col[u] == 0: rem2.append((u, v))
    else: rem2.append((v, u))
rs = set(map(tuple, map(sorted, rem2)))
newE = [(u, v) for (u, v) in E if tuple(sorted((u, v))) not in rs]
a2, b2 = n, n+1
newE += [(a2, b) for a, b in rem2] + [(a, b2) for a, b in rem2]
with open(out, 'w') as f:
    f.write(f"{n+2}\n")
    for u, v in newE: f.write(f"{min(u,v)} {max(u,v)}\n")
print("ok", n+2, len(newE))
