#!/usr/bin/env python3
"""Re-coordinatise a voltage lift X = Lift(B, G) as an N-lift of the quotient base X/N for a subgroup N <= G.
Lift convention (vl.c): base edge (a,b,al) with a on side 0: (a,h) ~ (b, h*al).
G acts on X by left multiplication; N-orbits are right cosets N t. Representatives t_i, index i = 0..k-1.
New base vertex (a,i) ~ lift vertex (a, n t_i) with N-coordinate n. Edge (a,i)-(b,j) with voltage nu where
t_i*al = nu * t_j.
usage: subquot.py SOL GROUP NELEMS OUTBASE OUTGROUP   (NELEMS: comma list of G-element indices of N, containing 0)
Writes OUTBASE (vl format, un-normalised) and OUTGROUP (table of N in local indices, identity = 0)."""
import sys
sol, grp, nel, obase, ogroup = sys.argv[1:6]
tok = open(grp).read().split(); m = int(tok[0])
mul = [list(map(int, tok[1 + i*m:1 + (i+1)*m])) for i in range(m)]
inv = [r.index(0) for r in mul]
N = [0] + sorted(set(int(x) for x in nel.split(',') if int(x) != 0))
Nset = set(N); k = m // len(N); assert m % len(N) == 0
# cosets N g
coset = [-1] * m; reps = []
for g in range(m):
    if coset[g] < 0:
        ci = len(reps); reps.append(g)
        for n in N: coset[mul[n][g]] = ci
assert len(reps) == k, (len(reps), k)
L = [l for l in open(sol).read().split('\n') if l.strip() and not l.startswith('#')]
if L[0].startswith('SOL'): L[0] = L[0][3:]
b, E = map(int, L[0].split()); side = list(map(int, L[1].split()))
ed = [list(map(int, x.split())) for x in L[2:2 + E]]
for e in ed:
    if side[e[0]] == 1:
        # reverse orientation: (b,h) ~ (a, h al^-1) with (b, h') representation
        e[0], e[1] = e[1], e[0]; e[2] = inv[e[2]]
loc = {g: i for i, g in enumerate(N)}
# local N table
with open(ogroup, 'w') as f:
    f.write(f"{len(N)}\n" + "".join(" ".join(str(loc[mul[a][c]]) for c in N) + "\n" for a in N))
nb = []
for (a, bb, al) in ed:
    for i, t in enumerate(reps):
        g = mul[t][al]           # t_i * al
        j = coset[g]; tj = reps[j]
        nu = mul[g][inv[tj]]     # g = nu * t_j  => nu = g t_j^-1 in N
        assert nu in Nset
        nb.append((a * k + i, bb * k + j, loc[nu]))
side2 = [side[v // k] for v in range(b * k)]
with open(obase, 'w') as f:
    f.write(f"{b*k} {len(nb)}\n" + " ".join(map(str, side2)) + "\n" + "".join(f"{u} {w} {g}\n" for u, w, g in nb))
print(f"base {b*k}+{b*k} vertices... {b*k} total, {len(nb)} edges, |N|={len(N)}, index {k}")
