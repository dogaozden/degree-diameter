# Enumerate connected cubic bipartite multigraph bases (k x k nonneg integer matrices, row/col sums 3)
# up to row and column permutations (canonical form by brute force over permutations).
import itertools, sys, os
k = int(sys.argv[1]); outdir = sys.argv[2]
rows = [r for r in itertools.product(range(4), repeat=k) if sum(r) == 3]
perms = list(itertools.permutations(range(k)))
def connected(M):
    adj = {('A', i): [] for i in range(k)}; adj.update({('B', j): [] for j in range(k)})
    for i in range(k):
        for j in range(k):
            if M[i][j]: adj[('A', i)].append(('B', j)); adj[('B', j)].append(('A', i))
    seen = {('A', 0)}; st = [('A', 0)]
    while st:
        x = st.pop()
        for y in adj[x]:
            if y not in seen: seen.add(y); st.append(y)
    return len(seen) == 2 * k
def canon(M):
    best = None
    for p in perms:
        for q in perms:
            N = tuple(tuple(M[p[i]][q[j]] for j in range(k)) for i in range(k))
            if best is None or N < best: best = N
    return best
seen = set(); res = []
for combo in itertools.product(rows, repeat=k):
    if any(sum(combo[i][j] for i in range(k)) != 3 for j in range(k)): continue
    M = [list(r) for r in combo]
    if not connected(M): continue
    c = canon(M)
    if c in seen: continue
    seen.add(c); res.append(c)
print(k, "classes:", len(res))
os.makedirs(outdir, exist_ok=True)
for idx, M in enumerate(res):
    edges = [(i, j) for i in range(k) for j in range(k) for _ in range(M[i][j])]
    fn = os.path.join(outdir, f"b{k}{k}_{idx}.txt")
    with open(fn, "w") as f:
        f.write(f"{2*k} {len(edges)}\n")
        for i, j in edges: f.write(f"{i} {k+j}\n")
    print(fn, M, "doubles:", sum(1 for i in range(k) for j in range(k) if M[i][j] == 2), "triples:", sum(1 for i in range(k) for j in range(k) if M[i][j] == 3))
