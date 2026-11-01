# Random simple d-regular bipartite graphs on 2N vertices (union of d perfect matchings, rejection per matching).
import random, sys
def reg_bip(N, d, seed):
    rnd = random.Random(seed)
    edges = set()
    for _ in range(d):
        while True:
            perm = list(range(N)); rnd.shuffle(perm)
            new = [(i, N + perm[i]) for i in range(N)]
            if not any(e in edges for e in new):
                edges.update(new); break
    return sorted(edges)
def write(path, N, d, seed):
    E = reg_bip(N, d, seed)
    with open(path, "w") as f:
        f.write(f"{2*N}\n")
        for u, v in E: f.write(f"{u} {v}\n")
    print(path, "n", 2*N, "edges", len(E), "d", d)
write("rand3_170.edges", 85, 3, 1)
write("rand6_686.edges", 343, 6, 2)
