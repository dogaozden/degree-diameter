#!/usr/bin/env python3
"""Export a tabu lift (tabu OUT file: "b E", side line, "u w volt" lines; u on side 0) to an edge list.
usage: export_c2.py SOL GROUP OUT_EDGES.  Lift vertex (v,h) = v*m + h; base edge (u,w,g): (u,h) ~ (w, h*g)."""
import sys
sol, grp, out = sys.argv[1:4]
with open(grp) as f:
    tok = f.read().split()
m = int(tok[0])
mul = [list(map(int, tok[1 + i * m:1 + (i + 1) * m])) for i in range(m)]
with open(sol) as f:
    lines = [l.split() for l in f if l.strip() and not l.startswith("#")]
b, E = int(lines[0][0]), int(lines[0][1])
side = list(map(int, lines[1][:b]))
edges = []
for t in lines[2:2 + E]:
    u, w, g = int(t[0]), int(t[1]), int(t[2]) if len(t) > 2 else 0
    if side[u] == 1:
        u, w = w, u
    for h in range(m):
        edges.append((u * m + h, w * m + mul[h][g]))
n = b * m
with open(out, "w") as f:
    f.write(f"{n}\n")
    for a, c in edges:
        f.write(f"{a} {c}\n")
print("n", n, "edges", len(edges))
