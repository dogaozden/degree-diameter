# enumerate connected cubic bipartite multigraphs on 4+4 vertices (4x4 nonneg int matrices, row/col sums 3), up to row/col perms
import itertools, sys
def mats():
    rows = [r for r in itertools.product(range(4), repeat=4) if sum(r) == 3]
    for a in rows:
        for b in rows:
            for c in rows:
                s = [a[i]+b[i]+c[i] for i in range(4)]
                # 4th row determined
                d = tuple(3 - s[i] for i in range(4))
                if sum(d) != 3 or min(d) < 0: continue
                yield (a, b, c, d)
def connected(M):
    adj = {('A', i): [] for i in range(4)}; adj.update({('B', j): [] for j in range(4)})
    for i in range(4):
        for j in range(4):
            for _ in range(M[i][j]):
                adj[('A', i)].append(('B', j)); adj[('B', j)].append(('A', i))
    seen = {('A', 0)}; st = [('A', 0)]
    while st:
        x = st.pop()
        for y in adj[x]:
            if y not in seen: seen.add(y); st.append(y)
    return len(seen) == 8
def canon(M):
    best = None
    for p in itertools.permutations(range(4)):
        for q in itertools.permutations(range(4)):
            key = tuple(tuple(M[p[i]][q[j]] for j in range(4)) for i in range(4))
            if best is None or key < best: best = key
    return best
classes = {}
for M in mats():
    if not connected(M): continue
    c = canon(M)
    classes.setdefault(c, 0)
    classes[c] += 1
print(len(classes), file=sys.stderr)
import os
os.makedirs('bases', exist_ok=True)
for idx, c in enumerate(sorted(classes)):
    edges = []
    for i in range(4):
        for j in range(4):
            edges += [(i, 4 + j)] * c[i][j]
    name = f'bases/q{idx:02d}.txt'
    with open(name, 'w') as f:
        f.write(f'8 {len(edges)}\n')
        for u, v in edges: f.write(f'{u} {v}\n')
    print(name, c)
