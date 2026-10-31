# usage: python3 -I mkbase_z7.py B SEED OUT GROUP_OUT m : random 6-regular bipartite base on B+B vertices
# (union of 6 random perfect matchings, no parallel edges), and the cyclic group Z_m table (m x m, element 0 = identity)
import sys, random
B = int(sys.argv[1]); seed = int(sys.argv[2]); out = sys.argv[3]; gout = sys.argv[4]; m = int(sys.argv[5])
random.seed(seed)
edges = set()
while True:
    edges = set()
    ok = True
    for _ in range(6):
        for _try in range(200):
            perm = list(range(B)); random.shuffle(perm)
            new = [(u, B + perm[u]) for u in range(B)]
            if all(e not in edges for e in new):
                edges.update(new); break
        else:
            ok = False
    if ok and len(edges) == 6 * B:
        break
edges = sorted(edges)
with open(out, 'w') as f:
    f.write(f"{2*B} {len(edges)}\n")
    f.write(" ".join(["0"] * B + ["1"] * B) + "\n")
    for u, w in edges:
        f.write(f"{u} {w} {random.randrange(m)}\n")
with open(gout, 'w') as f:
    f.write(f"{m}\n")
    for a in range(m):
        f.write(" ".join(str((a + b) % m) for b in range(m)) + "\n")
print("base", out, "vertices", 2*B, "edges", len(edges))
