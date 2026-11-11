# gen_base.py: incidence graph of H(3) from seeds/hexagon_q3.json -> base.edges (points 0..363, lines 364..727)
import json, sys
d = json.load(open('/home/user/degree-diameter/research/squads/handsoff-49/seeds/hexagon_q3.json'))
P = d['points']; L = d['lines']
edges = []
for j, ln in enumerate(L):
    for p in ln:
        edges.append((p, P + j))
with open('base.edges', 'w') as f:
    f.write(f"{P + len(L)}\n")
    for u, v in edges:
        f.write(f"{u} {v}\n")
# plain base file for lift.c style tools: "b m" then "u v"
with open('base.txt', 'w') as f:
    f.write(f"{P + len(L)} {len(edges)}\n")
    for u, v in edges:
        f.write(f"{u} {v}\n")
deg = [0] * (P + len(L))
for u, v in edges:
    deg[u] += 1; deg[v] += 1
print("vertices", P + len(L), "edges", len(edges), "degs", set(deg), "dup", len(edges) - len(set(edges)))
