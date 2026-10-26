# Enumerate connected cubic bipartite multigraphs on 3+3 vertices (3x3 nonnegative integer matrices, row/col sums 3),
# up to row/column permutations. Writes base files b1.txt, b2.txt, ... in this folder (flift format: "b m" then edges).
import itertools, sys, os
OUT = "/home/user/degree-diameter/research/squads/b48/r5/k10"
rows = [r for r in itertools.product(range(4), repeat=3) if sum(r) == 3]
mats = [m for m in itertools.product(rows, repeat=3) if all(sum(m[i][j] for i in range(3)) == 3 for j in range(3))]
def canon(M):
    best = None
    for p in itertools.permutations(range(3)):
        for q in itertools.permutations(range(3)):
            t = tuple(tuple(M[p[i]][q[j]] for j in range(3)) for i in range(3))
            if best is None or t < best: best = t
    return best
def connected(M):
    seen = {('a', 0)}; st = [('a', 0)]
    while st:
        s, i = st.pop()
        nb = [('b', j) for j in range(3) if M[i][j] > 0] if s == 'a' else [('a', k) for k in range(3) if M[k][i] > 0]
        for x in nb:
            if x not in seen: seen.add(x); st.append(x)
    return len(seen) == 6
cls = {}
for M in mats:
    c = canon(M)
    cls[c] = connected(M)
reps = sorted(c for c in cls if cls[c])
print("connected classes:", len(reps), file=sys.stderr)
for idx, M in enumerate(reps, 1):
    edges = []
    for i in range(3):
        for j in range(3):
            edges += [(i, 3 + j)] * M[i][j]
    assert len(edges) == 9
    fn = os.path.join(OUT, f"b{idx}.txt")
    with open(fn, "w") as f:
        f.write(f"6 9\n")
        for u, v in edges: f.write(f"{u} {v}\n")
    print(idx, M, "multi-edges:", sum(1 for x in M for y in x if y > 1), file=sys.stderr)
