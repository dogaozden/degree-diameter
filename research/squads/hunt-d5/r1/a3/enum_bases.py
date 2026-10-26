import itertools, os
# enumerate 3x3 nonnegative integer matrices, row and column sums 5, up to row/column permutations
def mats():
    rows = [r for r in itertools.product(range(6), repeat=3) if sum(r) == 5]
    for a in rows:
        for b in rows:
            for c in rows:
                if all(a[j]+b[j]+c[j] == 5 for j in range(3)):
                    yield (a, b, c)
seen = {}
for M in mats():
    best = None
    for p in itertools.permutations(range(3)):
        for q in itertools.permutations(range(3)):
            N = tuple(tuple(M[p[i]][q[j]] for j in range(3)) for i in range(3))
            if best is None or N < best: best = N
    seen.setdefault(best, 0)
print(len(seen), "bases up to iso")
os.makedirs("bases", exist_ok=True)
for k, M in enumerate(sorted(seen)):
    edges = []
    for i in range(3):
        for j in range(3):
            edges += [(i, 3 + j)] * M[i][j]
    fn = f"bases/b{k:02d}.txt"
    with open(fn, "w") as f:
        f.write(f"6 {len(edges)}\n")
        for u, v in edges: f.write(f"{u} {v}\n")
    print(fn, M, "maxmult", max(max(r) for r in M))
