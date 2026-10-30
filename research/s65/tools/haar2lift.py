#!/usr/bin/env python3
"""Write a Haar graph H(G,S) ((g,A) ~ (s g,B)) as a regular voltage lift of a 2+2 base by an index-2 subgroup N.
N = <squares> if that has index 2 (else the first index-2 subgroup containing it and the smallest outside element).
Orbits of N (right multiplication): A0 = (N,A), A1 = (tN,A), B0 = (N,B), B1 = (tN,B). Lift vertex (u,h) = (c x, side),
h = x^-1; edge (c x, A) ~ (s c x, B) with s c = c' y gives base edge u -> u' with voltage y^-1 (vl.c convention).
usage: haar2lift.py GROUP "S ..." OUTBASE OUTGROUP     (GROUP: m, table, anything after is ignored)"""
import sys
grp, Ss, obase, ogroup = sys.argv[1:5]
tok = open(grp).read().split(); m = int(tok[0])
mul = [list(map(int, tok[1 + i * m:1 + (i + 1) * m])) for i in range(m)]
inv = [r.index(0) for r in mul]
def closure(gens):
    H = {0}; frontier = [0]
    while frontier:
        x = frontier.pop()
        for g in gens:
            y = mul[x][g]
            if y not in H: H.add(y); frontier.append(y)
    return H
N = closure({mul[g][g] for g in range(m)})
if len(N) * 2 < m:   # extend by outside elements until index 2
    for g in range(m):
        if g not in N:
            H = closure(set(N) | {g})
            if len(H) * 2 == m: N = H; break
assert len(N) * 2 == m, "no index-2 subgroup"
t = next(g for g in range(m) if g not in N)
Nl = sorted(N); idx = {g: k for k, g in enumerate(Nl)}
S = list(map(int, Ss.split()))
edges = []
for ui, c in ((0, 0), (1, t)):
    for s in S:
        z = mul[s][c]
        if z in N: w, y = 2, z
        else: w, y = 3, mul[inv[t]][z]
        edges.append((ui, w, idx[inv[y]]))
with open(obase, 'w') as f:
    f.write(f"4 {len(edges)}\n0 0 1 1\n" + "".join(f"{u} {w} {g}\n" for u, w, g in edges))
with open(ogroup, 'w') as f:
    f.write(f"{len(Nl)}\n" + "".join(" ".join(str(idx[mul[a][b]]) for b in Nl) + "\n" for a in Nl))
print(f"wrote {obase}, {ogroup}: |N| = {len(Nl)}, t = {t}, multiplicities", sorted((u, w) for u, w, _ in edges))
