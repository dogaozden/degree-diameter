# Enumerate 4-regular bipartite multigraphs on 4+4 vertices (4x4 nonneg integer matrices, row/col sums 4),
# up to row and column permutations. Write each class as a base file for lift ("8 16" then 16 edge lines).
import itertools, os
OUT = "/home/user/degree-diameter/research/squads/b48/r1/c21/bases"
rows4 = [r for r in itertools.product(range(5), repeat=4) if sum(r) == 4]
mats = []
for r0, r1, r2, r3 in itertools.product(rows4, repeat=4):
    M = (r0, r1, r2, r3)
    if all(sum(M[i][j] for i in range(4)) == 4 for j in range(4)):
        mats.append(M)
perms = list(itertools.permutations(range(4)))
def canon(M):
    best = None
    for p in perms:
        Mp = [M[p[i]] for i in range(4)]
        for q in perms:
            X = tuple(tuple(Mp[i][q[j]] for j in range(4)) for i in range(4))
            if best is None or X < best:
                best = X
    return best
classes = sorted(set(canon(M) for M in mats))
print("labelled matrices", len(mats), "classes", len(classes))
for ci, M in enumerate(classes):
    edges = []
    for i in range(4):
        for j in range(4):
            edges += [(i, 4 + j)] * M[i][j]
    name = os.path.join(OUT, "k4_%02d.txt" % ci)
    with open(name, "w") as f:
        f.write("8 %d\n" % len(edges))
        for u, v in edges:
            f.write("%d %d\n" % (u, v))
    simple = all(x <= 1 for r in M for x in r)
    print(ci, os.path.basename(name), "rows", ["".join(map(str, r)) for r in M], "simple" if simple else "multi", "maxmult", max(max(r) for r in M))
