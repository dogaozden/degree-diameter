# usage: liftedges.py TABLE.tab SOL OUT_EDGES  -- lift a salift .sol (N id p, then 3p lines "u v a") to an edge list
# vertex (u,g) = u*N+g; base edge (u,v,a) gives (u,g) ~ (v, g*a) with the table product mul[g*N+a].
import sys
tab, sol, out = sys.argv[1:4]
with open(tab) as f:
    N = int(f.readline().split()[1])
    mul = []
    for line in f:
        mul.extend(map(int, line.split()))
with open(sol) as f:
    N2, gid, p = map(int, f.readline().split()[:3])
    assert N2 == N, (N2, N)
    E = [tuple(map(int, l.split())) for l in f if l.strip()]
k = 2 * p; n = k * N
edges = set()
for (u, v, a) in E:
    for g in range(N):
        x = u * N + g; y = v * N + mul[g * N + a]
        edges.add((min(x, y), max(x, y)))
assert len(edges) == len(E) * N, "parallel edges or duplicates"
deg = [0] * n
for x, y in edges: deg[x] += 1; deg[y] += 1
assert all(d == 3 for d in deg), "not cubic"
with open(out, 'w') as f:
    f.write(f"{n}\n")
    for x, y in sorted(edges): f.write(f"{x} {y}\n")
print("n", n, "edges", len(edges), "cubic ok")
