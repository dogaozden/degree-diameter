import sys, numpy as np
sys.path.insert(0, "/home/user/degree-diameter/research/squads/b48/tools")
import groups
rng = np.random.default_rng(5)
for spec in ["dih 3 x dih 92", "dih 5 x dih 55", "sl2 3 x dih 23", "dih 3 x dih 3 x cyc 31", "meta 7 3 2 x dih 27"]:
    T = groups.table(spec); N = len(T)
    # associativity on random triples
    ok = True
    for _ in range(3000):
        a, b, c = rng.integers(0, N, 3)
        if T[T[a, b], c] != T[a, T[b, c]]: ok = False; break
    # generated subgroup of random 4-sets (S and inverses), BFS size
    inv = np.array([int(np.where(T[g] == 0)[0][0]) for g in range(N)])
    sizes = []
    for _ in range(5):
        S = rng.integers(0, N, 4)
        H = {0}; frontier = [0]
        gens = list(S) + [int(inv[s]) for s in S]
        while frontier:
            x = frontier.pop()
            for g in gens:
                y = int(T[x, g])
                if y not in H: H.add(y); frontier.append(y)
        sizes.append(len(H))
    print(spec, N, "assoc", ok, "subgroup sizes of random 4-sets", sizes, flush=True)
