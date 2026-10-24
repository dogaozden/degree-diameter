#!/usr/bin/env python3
# Random pgl test solution (card B3 validation only): python3 -I mk_random.py p n d seed D OUTFILE
# Writes "d D pgl p n n N N" and d distinct random generators "i mat(a,b,c,d) z=Z" (canonical PGL(2,p) reps).
import random
import sys

p, n, d, seed, D = (int(x) for x in sys.argv[1:6])
out = sys.argv[6]
rng = random.Random(seed)
els = []
for a in range(p):
    for b in range(p):
        for c in range(p):
            for dd in range(p):
                if (a * dd - b * c) % p == 0:
                    continue
                if (a if a else b) != 1:          # canonical: first nonzero of (a,b) is 1
                    continue
                els.append((a, b, c, dd))
N = len(els) * n
gens = set()
while len(gens) < d:
    gens.add((rng.randrange(len(els)), rng.randrange(n)))
gens = sorted(gens, key=lambda t: rng.random())
with open(out, "w") as f:
    f.write(f"{d} {D} pgl {p} n {n} N {N}\n")
    for i, (qi, z) in enumerate(gens):
        a, b, c, dd = els[qi]
        f.write(f"{i + 1} mat({a},{b},{c},{dd}) z={z}\n")
print("wrote", out, "N =", N, "vertices =", 2 * N)
