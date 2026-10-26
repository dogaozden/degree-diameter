# Enumerate connected 4-regular bipartite multigraphs on 3+3 vertices (3x3 nonneg int matrices, row and col sums 4),
# up to row perms, column perms and transpose. Writes bases/bNN.txt in lift format ("6 12", then 12 lines "u v").
import itertools, os, sys
OUT = "/home/user/degree-diameter/research/squads/b48/r1/c20/bases"
rows = []
for a in itertools.product(range(5), repeat=3):
    if sum(a) == 4: rows.append(a)
mats = []
for r0, r1, r2 in itertools.product(rows, repeat=3):
    M = (r0, r1, r2)
    if all(sum(M[i][j] for i in range(3)) == 4 for j in range(3)):
        mats.append(M)
def canon(M):
    best = None
    for T in (False, True):
        A = [[M[j][i] for j in range(3)] for i in range(3)] if T else [list(r) for r in M]
        for p in itertools.permutations(range(3)):
            for q in itertools.permutations(range(3)):
                key = tuple(tuple(A[p[i]][q[j]] for j in range(3)) for i in range(3))
                if best is None or key < best: best = key
    return best
def connected(M):
    # bipartite support graph on rows 0..2 and cols 0..2
    seen = {('r', 0)}; st = [('r', 0)]
    while st:
        t, i = st.pop()
        nb = [('c', j) for j in range(3) if M[i][j] > 0] if t == 'r' else [('r', k) for k in range(3) if M[k][i] > 0]
        for x in nb:
            if x not in seen: seen.add(x); st.append(x)
    return len(seen) == 6
classes = {}
for M in mats:
    if not connected(M): continue
    c = canon(M)
    classes.setdefault(c, M)
os.makedirs(OUT, exist_ok=True)
for f in os.listdir(OUT): os.remove(os.path.join(OUT, f))
names = []
for idx, c in enumerate(sorted(classes)):
    name = "b33_%02d" % idx
    lines = ["6 12"]
    for i in range(3):
        for j in range(3):
            for _ in range(c[i][j]):
                lines.append("%d %d" % (i, 3 + j))
    with open(os.path.join(OUT, name + ".txt"), "w") as f: f.write("\n".join(lines) + "\n")
    names.append((name, c))
for name, c in names:
    print(name, c, "max_mult=%d" % max(max(r) for r in c), "simple" if max(max(r) for r in c) == 1 else "")
print("count", len(names))
