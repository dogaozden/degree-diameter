# 686 start with two covering new vertices: u (side A) adjacent to w_1..w_6 (B), v (side B) adjacent to z_1..z_6 (A),
# where (w_i, z_i) are edges of the 684 Haar graph that are removed. Search: random greedy over edges so that
# union of 3-balls of the w_i covers all of A and union of 3-balls of the z_i covers all of B.
import sys, random
from collections import deque
random.seed(int(sys.argv[1])); out = sys.argv[2]; TRIALS = int(sys.argv[3]) if len(sys.argv) > 3 else 20000
t = open('../c7/h684.edges').read().split(); n = int(t[0]); E = [(int(t[i]), int(t[i+1])) for i in range(1, len(t), 2)]
adj = [[] for _ in range(n)]
for a, b in E: adj[a].append(b); adj[b].append(a)
col = [-1]*n; col[0] = 0; q = deque([0])
while q:
    x = q.popleft()
    for y in adj[x]:
        if col[y] < 0: col[y] = 1-col[x]; q.append(y)
A = set(v for v in range(n) if col[v] == 0); B = set(v for v in range(n) if col[v] == 1)
def ball3(w):
    d = {w: 0}; fr = [w]
    for depth in range(1, 4):
        nf = []
        for x in fr:
            for y in adj[x]:
                if y not in d: d[y] = depth; nf.append(y)
        fr = nf
    return frozenset(d)
B3 = {v: ball3(v) for v in range(n)}
edges = [(a, b) if col[a] == 0 else (b, a) for a, b in E]   # (z in A, w in B)
best = None
for trial in range(TRIALS):
    chosen = []; covA = set(); covB = set(); used_w = set(); used_z = set()
    for k in range(6):
        bestsc = None
        for _ in range(80):
            z, w = random.choice(edges)
            if w in used_w or z in used_z: continue
            ca = len(covA | (B3[w] & A)); cb = len(covB | (B3[z] & B))
            sc = ca + cb + random.random()
            if bestsc is None or sc > bestsc[0]: bestsc = (sc, z, w)
        if bestsc is None: break
        _, z, w = bestsc
        chosen.append((z, w)); used_w.add(w); used_z.add(z)
        covA |= (B3[w] & A); covB |= (B3[z] & B)
    score = len(covA) + len(covB)
    if best is None or score > best[0]:
        best = (score, chosen, len(covA), len(covB))
        print("trial", trial, "covA", len(covA), "covB", len(covB), flush=True)
    if len(covA) == len(A) and len(covB) == len(B): break
score, chosen, ca, cb = best
print("BEST covA", ca, "of", len(A), "covB", cb, "of", len(B), flush=True)
rem = set(tuple(sorted(e)) for e in E)
Enew = set(rem)
for z, w in chosen: Enew.discard(tuple(sorted((z, w))))
u = n; v = n + 1
for z, w in chosen:
    Enew.add(tuple(sorted((w, u)))); Enew.add(tuple(sorted((z, v))))
with open(out, 'w') as f:
    f.write("%d\n" % (n + 2))
    for a, b in sorted(Enew): f.write("%d %d\n" % (a, b))
print("wrote", out, "edges", len(Enew))
