# one extra vertex x (side of colour 1): delete K matchings-worth of edges (a,b), attach x to the a's.
# All degrees stay <= Delta; the b's that lost an edge become deficient (degree Delta-1).
# usage: grow1.py IN OUT DELTA SEED
import random, sys
inp, out, delta, seed = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
random.seed(seed)
L = [l for l in open(inp) if l.strip()]
n = int(L[0]); E = [tuple(map(int, l.split()[:2])) for l in L[1:]]
adj = {v: set() for v in range(n)}
for u, v in E: adj[u].add(v); adj[v].add(u)
col = [-1] * n; col[0] = 0; st = [0]
while st:
    x = st.pop()
    for y in adj[x]:
        if col[y] < 0: col[y] = 1 - col[x]; st.append(y)
Es = set((u, v) if col[u] == 0 else (v, u) for u, v in E)
while True:
    cand = random.sample(sorted(Es), 400)
    used = set(); M = []
    for (a, b) in cand:
        if a in used or b in used: continue
        M.append((a, b)); used |= {a, b}
        if len(M) == delta: break
    if len(M) == delta: break
x = n; n += 1
for (a, b) in M:
    Es.discard((a, b)); Es.add((a, x))
with open(out, 'w') as f:
    f.write(f"{n}\n")
    for (a, b) in sorted(Es): f.write(f"{a} {b}\n")
print(f"n={n} edges={len(Es)}")
