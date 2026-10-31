#!/usr/bin/env python3
"""Write a Haar graph H(G,S) ((g,A) ~ (s g,B)) as a regular voltage lift of an h+h base by a subgroup N of index h
(N acts freely by right multiplication; orbits = left cosets t_i N on each side). Edge (t_i x, A) ~ (s t_i x, B), with
s t_i = t_j y (y in N), becomes base edge A_i -> B_j with voltage y^-1 (vl.c convention, lift vertex (u, x^-1)).
usage: haar2liftN.py GROUP NFILE "S ..." OUTBASE OUTGROUP   (NFILE: element indices of N, any order, containing 0)"""
import sys
grp, nfile, Ss, obase, ogroup = sys.argv[1:6]
tok = open(grp).read().split(); m = int(tok[0])
mul = [list(map(int, tok[1 + i * m:1 + (i + 1) * m])) for i in range(m)]
inv = [r.index(0) for r in mul]
N = sorted(set(map(int, open(nfile).read().replace("\\\n", "").split()))); Ns = set(N); h = m // len(N)
reps = []; covered = set()
for g in range(m):
    if g not in covered:
        reps.append(g); covered |= {mul[g][x] for x in N}
assert len(reps) == h
idx = {g: k for k, g in enumerate(N)}
S = list(map(int, Ss.split())); edges = []
for i, t in enumerate(reps):
    for s in S:
        z = mul[s][t]
        j = next(j for j, tj in enumerate(reps) if mul[inv[tj]][z] in Ns)
        y = mul[inv[reps[j]]][z]
        edges.append((i, h + j, idx[inv[y]]))
with open(obase, 'w') as f:
    f.write(f"{2 * h} {len(edges)}\n" + " ".join(["0"] * h + ["1"] * h) + "\n" + "".join(f"{u} {w} {g}\n" for u, w, g in edges))
with open(ogroup, 'w') as f:
    f.write(f"{len(N)}\n" + "".join(" ".join(str(idx[mul[a][b]]) for b in N) + "\n" for a in N))
print(f"wrote {obase} ({2*h} base vertices, {len(edges)} edges), {ogroup} (|N| = {len(N)})")
