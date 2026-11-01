# random 4-regular bipartite graph on N+N vertices as the union of 4 random perfect matchings (retry on multi-edges)
import random, sys
N = int(sys.argv[1]); seed = int(sys.argv[2]); random.seed(seed)
while True:
    edges = set(); ok = True
    for _ in range(4):
        p = list(range(N)); random.shuffle(p)
        for a in range(N):
            e = (a, N + p[a])
            if e in edges: ok = False; break
            edges.add(e)
        if not ok: break
    if ok: break
with open(sys.argv[3], "w") as f:
    f.write(f"{2*N}\n")
    for a, b in sorted(edges): f.write(f"{a} {b}\n")
print("written", len(edges))
