# Incidence graph of PG(2,5): points and lines are the normalised nonzero triples over Z_5 (first nonzero = 1).
# Point j is on line k iff the dot product is 0 mod 5. Writes pg25.hg: "K m" then m lines "j k" (mode-3 hub graph).
import itertools
P = 5
pts = []
for v in itertools.product(range(P), repeat=3):
    if any(v):
        first = next(x for x in v if x)
        if first == 1:
            pts.append(v)
assert len(pts) == 31, len(pts)
edges = [(j, k) for j, a in enumerate(pts) for k, b in enumerate(pts)
         if sum(x * y for x, y in zip(a, b)) % P == 0]
deg_pt = [sum(1 for j, _ in edges if j == i) for i in range(31)]
deg_ln = [sum(1 for _, k in edges if k == i) for i in range(31)]
assert len(edges) == 186 and set(deg_pt) == {6} and set(deg_ln) == {6}
# any two distinct points lie on exactly one common line (projective plane)
lines_of = {j: {k for jj, k in edges if jj == j} for j in range(31)}
assert all(len(lines_of[a] & lines_of[b]) == 1 for a in range(31) for b in range(a + 1, 31))
with open("pg25.hg", "w") as f:
    f.write(f"31 {len(edges)}\n")
    for j, k in edges:
        f.write(f"{j} {k}\n")
print("wrote pg25.hg: K=31, m=186, hub degree 6, every pair of hubs on one side has a common neighbour")
