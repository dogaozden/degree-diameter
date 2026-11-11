"""All connected 4-regular bipartite multigraphs with h+h vertices (matrix M, row and column sums 4, entries <= 4),
up to row/column permutations (canonical form = lexicographically smallest sorted-rows representation).
Writes bases/mh{h}_{idx}.txt in flift format (vertices 0..h-1 side A, h..2h-1 side B; edge u v per matrix unit).
Usage: python3 gen_matrix_bases.py H [max_bases]"""
import sys, os, itertools
H = int(sys.argv[1]); cap = int(sys.argv[2]) if len(sys.argv) > 2 else 10**9
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bases")
def rows_of(h, s):   # all rows of length h, entries 0..4, sum s
    if h == 0:
        if s == 0: yield ()
        return
    for x in range(min(4, s) + 1):
        for r in rows_of(h - 1, s - x): yield (x,) + r
def connected(M, h):
    seen = {0}; st = [("A", 0)]; vis = {("A", 0)}
    while st:
        side, i = st.pop()
        if side == "A":
            nb = [("B", j) for j in range(h) if M[i][j]]
        else:
            nb = [("A", j) for j in range(h) if M[j][i]]
        for x in nb:
            if x not in vis: vis.add(x); st.append(x)
    return len(vis) == 2 * h
def canon(M, h):
    best = None
    for p in itertools.permutations(range(h)):
        for q in itertools.permutations(range(h)):
            T = tuple(tuple(M[p[i]][q[j]] for j in range(h)) for i in range(h))
            if best is None or T < best: best = T
    return best
seen = set(); bases = []
allrows = list(rows_of(H, 4))
for combo in itertools.product(allrows, repeat=H):
    if any(sum(combo[i][j] for i in range(H)) != 4 for j in range(H)): continue
    M = [list(r) for r in combo]
    if not connected(M, H): continue
    c = canon(M, H)
    if c in seen: continue
    seen.add(c); bases.append(c)
    if len(bases) >= cap: break
os.makedirs(OUT, exist_ok=True)
for idx, T in enumerate(bases):
    E = [(i, H + j) for i in range(H) for j in range(H) for _ in range(T[i][j])]
    with open(os.path.join(OUT, f"mh{H}_{idx}.txt"), "w") as f:
        f.write(f"{2*H} {len(E)}\n")
        for u, v in E: f.write(f"{u} {v}\n")
    print(f"mh{H}_{idx}", T)
print("count", len(bases))
