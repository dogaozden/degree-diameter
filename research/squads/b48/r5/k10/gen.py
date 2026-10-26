"""Voltage generator for flift eval (k10). Usage:
  gen.py BASE SPEC random COUNT SEED      -> COUNT random assignments (tree edges 0, free edges uniform)
  gen.py BASE SPEC classes                -> exhaustive: first free edge over conjugacy-class representatives,
                                              remaining free edges over all elements (reduction by conjugation)
Voltage lines: m integers in the BASE edge order (tree edges = 0)."""
import sys, random
sys.path.insert(0, "/home/user/degree-diameter/research/squads/b48/tools")
import groups
import numpy as np

def tree_edges(base_path):
    L = open(base_path).read().split("\n")
    b, m = map(int, L[0].split())
    E = [tuple(map(int, L[1 + i].split()[:2])) for i in range(m)]
    darts = {u: [] for u in range(b)}
    for i, (u, v) in enumerate(E):
        darts[u].append((v, i)); darts[v].append((u, i))
    seen = {0}; q = [0]; tree = set(); h = 0
    while h < len(q):
        u = q[h]; h += 1
        for v, i in darts[u]:
            if v not in seen:
                seen.add(v); tree.add(i); q.append(v)
    return E, tree

def conj_classes(T):
    N = T.shape[0]
    inv = [int(np.where(T[g] == 0)[0][0]) for g in range(N)]
    cls = [-1] * N; reps = []
    for g in range(N):
        if cls[g] >= 0: continue
        reps.append(g)
        for h in range(N):
            x = int(T[int(T[h, g]), inv[h]])  # h g h^-1
            cls[x] = g
    return reps

if __name__ == "__main__":
    base, spec, mode = sys.argv[1], sys.argv[2], sys.argv[3]
    T = groups.table(spec)
    N = T.shape[0]
    E, tree = tree_edges(base)
    free = [i for i in range(len(E)) if i not in tree]
    out = sys.stdout
    if mode == "random":
        cnt, seed = int(sys.argv[4]), int(sys.argv[5])
        rng = random.Random(seed)
        for _ in range(cnt):
            v = [0] * len(E)
            for i in free: v[i] = rng.randrange(N)
            out.write(" ".join(map(str, v)) + "\n")
    elif mode == "classes":
        reps = conj_classes(T)
        f0 = free[0]
        others = free[1:]
        sys.stderr.write(f"N={N} classes={len(reps)} free={free}\n")
        import itertools
        for g1 in reps:
            for tup in itertools.product(range(N), repeat=len(others)):
                v = [0] * len(E); v[f0] = g1
                for i, x in zip(others, tup): v[i] = x
                out.write(" ".join(map(str, v)) + "\n")
