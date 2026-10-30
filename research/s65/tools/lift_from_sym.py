#!/usr/bin/env python3
"""Rewrite a graph with a fixed-point-free automorphism r of order R (acting with orbits of size R on both sides)
as a Z_R voltage lift (vl base + solution format), plus the Z_R group table.
usage: lift_from_sym.py EDGES R_FILE R OUT_SOL OUT_GROUP     (EDGES: n then 'a b', A = 0..nA-1; R_FILE: images)"""
import sys
ef, rf, R, osol, ogrp = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4], sys.argv[5]
L = open(ef).read().split('\n'); n = int(L[0]); E = [tuple(map(int, l.split()[:2])) for l in L[1:] if l.strip()]
rl = open(rf).read().split('\n'); rA = list(map(int, rl[0].split())); rB = list(map(int, rl[1].split()))
nA = len(rA); r = rA + [nA + x for x in rB]
lab = [None] * n; reps = []
for v in range(n):
    if lab[v] is not None: continue
    i = len(reps); reps.append(v); x = v
    for k in range(R):
        if lab[x] is not None: raise SystemExit("orbit not of size R")
        lab[x] = (i, k); x = r[x]
    if x != v: raise SystemExit("r does not have order R on this orbit")
b = len(reps); side = [0 if reps[i] < nA else 1 for i in range(b)]
base = set()
for (u, w) in E:
    (i, k), (j, l) = lab[u], lab[w]
    if side[i] == 1: (i, k), (j, l) = (j, l), (i, k)
    base.add((i, j, (l - k) % R))
base = sorted(base)
assert len(base) * R == len(E), (len(base), len(E))
with open(osol, 'w') as f:
    f.write(f"{b} {len(base)}\n" + " ".join(map(str, side)) + "\n")
    for (i, j, g) in base: f.write(f"{i} {j} {g}\n")
with open(ogrp, 'w') as f:
    f.write(f"{R}\n" + "".join(" ".join(str((x + y) % R) for y in range(R)) + "\n" for x in range(R)))
print("base vertices", b, "edges", len(base))
