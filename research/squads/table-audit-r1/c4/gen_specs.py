import sys
def write(name, nb, p, edges):
    with open(name, 'w') as f:
        f.write(f"{nb} {p}\n{len(edges)}\n")
        for u, w in edges:
            f.write(f"{u} {w}\n")
# K_{6,6}: 12 base vertices, 36 edges, degree 6
write('k66.spec', 12, 6, [(i, 6 + j) for i in range(6) for j in range(6)])
# K_{4,4}: 8 base vertices, degree 4
write('k44.spec', 8, 4, [(i, 4 + j) for i in range(4) for j in range(4)])
# 4-vertex bipartite multigraphs with degree 4
def mult(name, M):
    edges = []
    for i in range(2):
        for j in range(2):
            edges += [(i, 2 + j)] * M[i][j]
    write(name, 4, 2, edges)
mult('m2222.spec', [[2, 2], [2, 2]])
mult('m3113.spec', [[3, 1], [1, 3]])
# incidence graph of PG(2,5): 62 vertices, degree 6
q = 5
pts = []
for x in range(q):
    for y in range(q):
        for z in range(q):
            v = (x, y, z)
            if v == (0, 0, 0):
                continue
            first = next(c for c in v if c)
            if first == 1:
                pts.append(v)
assert len(pts) == 31
edges = [(i, 31 + j) for i, P in enumerate(pts) for j, L in enumerate(pts)
         if sum(a * b for a, b in zip(P, L)) % q == 0]
write('pg25.spec', 62, 31, edges)
print("specs written")
