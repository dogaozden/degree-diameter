#!/usr/bin/env python3
"""Surgery start: add K vertex pairs to a Delta-regular bipartite graph by deleting K random matchings of size Delta
(edge (a, b) deleted; new side-B vertex x_k ~ the a's, new side-A vertex y_k ~ the b's). All degrees stay <= Delta.
usage: grow.py IN_EDGES OUT_EDGES DELTA K SEED"""
import random, sys
inp, out, delta, K, seed = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
random.seed(seed)
lines = [l for l in open(inp) if l.strip() and not l.startswith('#')]
n = int(lines[0]); E = [tuple(map(int, l.split()[:2])) for l in lines[1:]]
adj = {v: set() for v in range(n)}
for u, v in E: adj[u].add(v); adj[v].add(u)
col = [-1] * n; col[0] = 0; st = [0]
while st:
    x = st.pop()
    for y in adj[x]:
        if col[y] < 0: col[y] = 1 - col[x]; st.append(y)
Es = set((u, v) if col[u] == 0 else (v, u) for u, v in E)
for k in range(K):
    while True:
        cand = random.sample(sorted(Es), 400)
        used = set(); M = []
        for (a, b) in cand:
            if a in used or b in used: continue
            M.append((a, b)); used |= {a, b}
            if len(M) == delta: break
        if len(M) == delta: break
    x, y = n, n + 1; n += 2
    for (a, b) in M:
        Es.discard((a, b)); Es.add((a, x)); Es.add((y, b))
with open(out, 'w') as f:
    f.write(f"{n}\n")
    for (a, b) in sorted(Es): f.write(f"{a} {b}\n")
print(f"n={n} edges={len(Es)}")
