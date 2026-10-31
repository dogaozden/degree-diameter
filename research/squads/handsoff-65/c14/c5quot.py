#!/usr/bin/env python3
"""N-lift (quotient by a semiregular subgroup N of G) of the c5 732 mcos graph (G = SmallGroup(366,2)).
A-side vertex x = element x; B-orbit j vertices = right cosets gH_j, H_j = <2> (mcos labelling), offsets 366+122j.
usage: c5quot.py ORDER_OF_N OUTBASE OUTGROUP   (N = unique subgroup of that order, must be coprime to 3)"""
import sys
ordN = int(sys.argv[1]); obase, ogroup = sys.argv[2], sys.argv[3]
tok = open('G366.txt').read().split(); m = int(tok[0])
mul = [list(map(int, tok[1 + i*m:1 + (i+1)*m])) for i in range(m)]
inv = [r.index(0) for r in mul]
def power(x, k):
    y = 0
    for _ in range(k): y = mul[y][x]
    return y
def order(x):
    k = 1; y = x
    while y != 0: y = mul[y][x]; k += 1
    return k
gen = next(x for x in range(m) if order(x) == ordN)
N = [0]; cur = 0
while True:
    cur = mul[cur][gen]
    if cur == 0: break
    N.append(cur)
assert len(N) == ordN, len(N)
Nset = set(N); loc = {g: i for i, g in enumerate(N)}
# graph
tk = open('../c5/deep/1_3-3-3.sg_366_2.best.edges').read().split()
n = int(tk[0]); E = [(int(tk[1+2*k]), int(tk[2+2*k])) for k in range((len(tk)-1)//2)]
off = [366, 488, 610]
cid = []; crep = []
for j in range(3):
    H = {0, 2, mul[2][2]}
    c = [-1]*m; reps = []
    for g in range(m):
        if c[g] < 0:
            k = len(reps); reps.append(g)
            for h in H: c[mul[g][h]] = k
    cid.append(c); crep.append(reps)
# vertex -> (class, n) with v = n * r_class (left action), classes: A-classes 0..(366/ordN)-1, then B classes
def vertex_coords(v):
    if v < 366:
        side = 0; base_idx = 0; elem = v
        grp_key = ('A', v)
    else:
        for j in range(3):
            if v < off[j] + len(crep[j]): break
        side = 1; elem = crep[j][v - off[j]]; grp_key = ('B', j, cid[j][elem])
    return side, grp_key, elem
# N-orbits on A: element x -> orbit {n x}; on B_j: coset cosets gH -> n g H
orbit_of = {}; reps_list = []
def orbit_id(key_fn, v):
    pass
# build classes by N action directly on vertices (as permutation on 732 vertices)
def act(nn, v):
    if v < 366: return mul[nn][v]
    for j in range(3):
        if v < off[j] + len(crep[j]): break
    k = v - off[j]; g = crep[j][k]
    return off[j] + cid[j][mul[nn][g]]
cls = [-1]*n; cls_rep = []; cls_coord = [None]*n
for v in range(n):
    if cls[v] < 0:
        c = len(cls_rep); cls_rep.append(v)
        for nn in N:
            w = act(nn, v)
            cls[w] = c
            cls_coord[w] = nn   # w = nn * rep
# verify coords: w = nn * rep (nn applied to rep)
nA = sum(1 for c in cls_rep if c is not None and c < len(cls_rep) and cls_rep[c] < 366)
# classes on side A: those whose rep < 366
side_of_class = [0 if r < 366 else 1 for r in cls_rep]
# relabel classes: A first, then B
order_cls = [c for c in range(len(cls_rep)) if side_of_class[c] == 0] + [c for c in range(len(cls_rep)) if side_of_class[c] == 1]
newid = {c: i for i, c in enumerate(order_cls)}
K = len(cls_rep)
tuples = set()
for (u, w) in E:
    if u >= 366: u, w = w, u
    cu, cw = cls[u], cls[w]
    nu, nw = cls_coord[u], cls_coord[w]
    beta = mul[inv[nu]][nw]
    assert beta in Nset
    tuples.add((newid[cu], newid[cw], loc[beta]))
tuples = sorted(tuples)
nb = len(cls_rep)
side2 = [0 if newid_inv == 0 else 0 for newid_inv in range(0)]
side2 = [0] * sum(1 for c in side_of_class if c == 0) + [1] * sum(1 for c in side_of_class if c == 1)
with open(obase, 'w') as f:
    f.write(f"{nb} {len(tuples)}\n" + " ".join(map(str, side2)) + "\n" + "".join(f"{a} {b} {g}\n" for a, b, g in tuples))
with open(ogroup, 'w') as f:
    f.write(f"{len(N)}\n" + "".join(" ".join(str(loc[mul[a][c]]) for c in N) + "\n" for a in N))
print("N", len(N), "base vertices", nb, "base edges", len(tuples), "A classes", side2.count(0), "B classes", side2.count(1))
