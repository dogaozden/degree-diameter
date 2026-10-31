#!/usr/bin/env python3
"""Random 6-regular bipartite multigraph base on p+p vertices, tabu format (b=2p, E=6p, side line, "u w 0" lines).
usage: mkbase.py P MODE SEED OUT   MODE: full = J + (6-P) random permutations (every pair adjacent, needs P<=6)
                                          rand = 6 random permutations (multi-edges and zero entries allowed)
Only connected bases are written."""
import random, sys

def perm_matrix(p, rng):
    perm = list(range(p)); rng.shuffle(perm)
    return [[1 if perm[i] == j else 0 for j in range(p)] for i in range(p)]

def connected(p, M):
    seen = {0}; stack = [0]
    while stack:
        x = stack.pop()
        if x < p:
            nbrs = [p + j for j in range(p) if M[x][j] > 0]
        else:
            nbrs = [i for i in range(p) if M[i][x - p] > 0]
        for y in nbrs:
            if y not in seen:
                seen.add(y); stack.append(y)
    return len(seen) == 2 * p

def make(p, mode, rng):
    while True:
        M = [[0] * p for _ in range(p)]
        if mode == "kminus":   # K_{p,p} minus (p-6) permutation matrices with pairwise disjoint supports (simple)
            M = [[1] * p for _ in range(p)]
            used = [[False] * p for _ in range(p)]
            ok = True
            for _ in range(p - 6):
                for _try in range(10000):
                    P = perm_matrix(p, rng)
                    if all(not (P[i][j] and used[i][j]) for i in range(p) for j in range(p)):
                        break
                else:
                    ok = False; break
                for i in range(p):
                    for j in range(p):
                        if P[i][j]:
                            used[i][j] = True; M[i][j] -= 1
            if not ok:
                continue
        elif mode == "full":
            for i in range(p):
                for j in range(p):
                    M[i][j] = 1
            for _ in range(6 - p):
                P = perm_matrix(p, rng)
                for i in range(p):
                    for j in range(p):
                        M[i][j] += P[i][j]
        else:
            for _ in range(6):
                P = perm_matrix(p, rng)
                for i in range(p):
                    for j in range(p):
                        M[i][j] += P[i][j]
        if connected(p, M):
            return M

def main():
    p, mode, seed, out = int(sys.argv[1]), sys.argv[2], int(sys.argv[3]), sys.argv[4]
    rng = random.Random(seed)
    M = make(p, mode, rng)
    edges = []
    for i in range(p):
        for j in range(p):
            edges += [(i, p + j)] * M[i][j]
    with open(out, "w") as f:
        f.write(f"{2*p} {len(edges)}\n")
        f.write(" ".join(["0"] * p + ["1"] * p) + "\n")
        for u, w in edges:
            f.write(f"{u} {w} 0\n")
    print(" ".join(" ".join(map(str, r)) for r in M))

if __name__ == "__main__":
    main()
