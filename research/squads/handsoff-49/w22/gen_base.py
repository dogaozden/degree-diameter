# Incidence graph of the split Cayley hexagon H(3): points 0..363, lines 364..727 (line j -> 364+j).
import json, sys
d = json.load(open(sys.argv[1]))
lines = d["lines"]
P = d["points"]
edges = []
for j, pts in enumerate(lines):
    for p in pts:
        edges.append((p, P + j))
n = 2 * P
with open(sys.argv[2], "w") as f:
    f.write(f"{n}\n")
    for u, v in edges:
        f.write(f"{u} {v}\n")
deg = [0] * n
for u, v in edges:
    deg[u] += 1; deg[v] += 1
print("n", n, "m", len(edges), "degs", set(deg))
