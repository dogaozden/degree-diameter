"""Connected cubic bipartite multigraphs on h+h vertices up to isomorphism (sides may be swapped).
Usage: python3 enum_bip3.py h OUTDIR   -> writes OUTDIR/b<2h>_<i>.txt in tlift base format ("k E", then "x y" edges,
white = 0..h-1, black = h..2h-1)."""
import itertools, sys, os

h = int(sys.argv[1]); out = sys.argv[2]
rows = [v for v in itertools.product(range(4), repeat=h) if sum(v) == 3]
mats = []

def rec(i, colres, cur):
    if i == h:
        if all(c == 0 for c in colres):
            mats.append(tuple(cur))
        return
    for v in rows:
        if all(v[j] <= colres[j] for j in range(h)):
            rec(i + 1, [colres[j] - v[j] for j in range(h)], cur + [v])

rec(0, [3] * h, [])

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
    perms = list(itertools.permutations(range(h)))
    for p in perms:
        Mp = [M[p[i]] for i in range(h)]
        for q in perms:
            C = tuple(tuple(Mp[i][q[j]] for j in range(h)) for i in range(h))
            if best is None or C < best:
                best = C
    return best

def transpose(M):
    return tuple(tuple(M[i][j] for i in range(h)) for j in range(h))

seen = {}
for M in mats:
    if not connected(M):
        continue
    c = canon(M)
    ct = canon(transpose(c))
    key = min(c, ct)
    seen[key] = True
classes = sorted(seen)
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
print("classes", len(classes), "matrices", len(mats))
