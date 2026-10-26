"""Connected cubic bipartite multigraphs on h+h vertices up to isomorphism (sides may be swapped), round 3.

Canonical form: for each row permutation, sort the columns (lexicographically as vectors); the minimum over row
permutations is a canonical form for row+column permutations. The class key is min(canon(M), canon(M^T)).
Usage: python3 enum3.py h OUTDIR   -> OUTDIR/b<2h>_<i>.txt in tlift base format ("k E", then "x y", white 0..h-1, black h..2h-1).
"""
import itertools, sys, os

h = int(sys.argv[1]); out = sys.argv[2]
vecs = [v for v in itertools.product(range(4), repeat=h) if sum(v) == 3]
perms = list(itertools.permutations(range(h)))


def connected(M):
    adj = {('w', i): [('b', j) for j in range(h) if M[i][j]] for i in range(h)}
    for j in range(h):
        adj[('b', j)] = [('w', i) for i in range(h) if M[i][j]]
    start = ('w', 0); seen = {start}; st = [start]
    while st:
        v = st.pop()
        for w in adj[v]:
            if w not in seen:
                seen.add(w); st.append(w)
    return len(seen) == 2 * h


def canon(M):
    best = None
    for p in perms:
        rows = [M[p[i]] for i in range(h)]
        cols = sorted(tuple(rows[i][j] for i in range(h)) for j in range(h))
        C = tuple(tuple(cols[j][i] for j in range(h)) for i in range(h))
        if best is None or C < best:
            best = C
    return best


def transpose(M):
    return tuple(tuple(M[i][j] for i in range(h)) for j in range(h))


classes = set()
raw = 0
# rows form a nondecreasing sequence (row order is free), columns must sum to 3
def rec(start, rows, colsum):
    global raw
    if len(rows) == h:
        if all(c == 3 for c in colsum):
            raw += 1
            M = tuple(rows)
            if connected(M):
                c = canon(M)
                classes.add(min(c, canon(transpose(c))))
        return
    for idx in range(start, len(vecs)):
        v = vecs[idx]
        if all(colsum[j] + v[j] <= 3 for j in range(h)):
            rec(idx, rows + [v], [colsum[j] + v[j] for j in range(h)])


rec(0, [], [0] * h)
classes = sorted(classes)
os.makedirs(out, exist_ok=True)
for idx, C in enumerate(classes):
    edges = []
    for i in range(h):
        for j in range(h):
            for _ in range(C[i][j]):
                edges.append((i, h + j))
    with open(os.path.join(out, f"b{2*h}_{idx}.txt"), "w") as f:
        f.write(f"{2*h} {len(edges)}\n")
        for x, y in edges:
            f.write(f"{x} {y}\n")
print("h", h, "classes", len(classes), "row-sorted matrices", raw)
