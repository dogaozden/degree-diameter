"""Convert a gen_group.py file (G1 table x Z_n) to the PGRP format of clhaarP.c (generators as left-multiplication
permutations). Generators: all elements (a, 0) of a random generating set of G1 plus (e, 1).
Usage: python3 grp2pgrp.py IN.grp OUT.pgrp"""
import sys, random
def main():
    tok = open(sys.argv[1]).read().split()
    N1, n, h, nsub = map(int, tok[:4]); pos = 4
    T = [list(map(int, tok[pos + a * N1: pos + (a + 1) * N1])) for a in range(N1)]; pos += N1 * N1
    subs = []
    for s in range(nsub):
        subs.append(list(map(int, tok[pos: pos + 1 + h]))); pos += 1 + h
    e = next(a for a in range(N1) if all(T[a][b] == b for b in range(N1)))
    rng = random.Random(1)
    # generating set of G1: add random elements until the closure is everything
    gens, reach = [], {e}
    while len(reach) < N1:
        g = rng.randrange(N1); gens.append(g)
        fr = list(reach)
        while fr:
            nf = []
            for x in fr:
                for k in gens:
                    y = T[k][x]
                    if y not in reach: reach.add(y); nf.append(y)
            fr = nf
    N = N1 * n
    perms = [[T[g][y // n] * n + y % n for y in range(N)] for g in gens]
    perms.append([(y // n) * n + (y % n + 1) % n for y in range(N)])
    with open(sys.argv[2], "w") as f:
        f.write(f"{N} {len(perms)} {e * n} {h} {nsub}\n")
        for p in perms: f.write(" ".join(map(str, p)) + "\n")
        for s in subs: f.write(" ".join(map(str, s)) + "\n")
    print(f"N={N} generators={len(perms)} -> {sys.argv[2]}")
main()
