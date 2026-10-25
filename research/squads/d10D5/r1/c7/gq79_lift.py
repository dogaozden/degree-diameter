#!/usr/bin/env python3
"""Card c7: Z6-lift of the generalized quadrangle GQ(7,9) = T2(O), O a hyperoval in PG(2,8).

Base graph (1,152 vertices): points = AG(3,8) (512, each on 10 lines), lines = affine lines with
direction in O (640, each with 8 points), so the incidence graph is biregular (10 | 8).
Lines have 2 spare degrees: a random Hamiltonian cycle on the lines (line-line edges, 2 per line).
Voltages in Z6: point-line edges in {0,2,4} (even), line-line edges in {1,3,5} (odd). Then the
lift is bipartite (colour = base side + Z2-part of the sheet), 10-regular, n = 6912.

usage: gq79_lift.py SEED OUT_EDGES
Writes the lift edge list (first line n, then "a b" per edge). Lift vertex = 6*b + h, base b < 512
is a point, b >= 512 a line.
"""
import random
import sys

MOD = 0b1011  # x^3 + x + 1 over GF(8)


def gmul(a, b):
    r = 0
    while b:
        if b & 1:
            r ^= a
        b >>= 1
        a <<= 1
        if a & 8:
            a ^= MOD
    return r


def det3(a, b, c):
    t1 = gmul(a[0], gmul(b[1], c[2]) ^ gmul(b[2], c[1]))
    t2 = gmul(a[1], gmul(b[0], c[2]) ^ gmul(b[2], c[0]))
    t3 = gmul(a[2], gmul(b[0], c[1]) ^ gmul(b[1], c[0]))
    return t1 ^ t2 ^ t3


# hyperoval: conic {(1,t,t^2)} plus nucleus (0,1,0) and (0,0,1)
O = [(1, t, gmul(t, t)) for t in range(8)] + [(0, 0, 1), (0, 1, 0)]
for i in range(len(O)):
    for j in range(i + 1, len(O)):
        for k in range(j + 1, len(O)):
            assert det3(O[i], O[j], O[k]) != 0, "hyperoval has 3 collinear points"


def idx(v):
    return v[0] * 64 + v[1] * 8 + v[2]


pts = [(x, y, z) for x in range(8) for y in range(8) for z in range(8)]
lines = []
for d in O:
    sd = [(gmul(s, d[0]), gmul(s, d[1]), gmul(s, d[2])) for s in range(8)]
    seen = set()
    for p in pts:
        mem = sorted(idx((p[0] ^ w[0], p[1] ^ w[1], p[2] ^ w[2])) for w in sd)
        if mem[0] in seen:
            continue
        seen.add(mem[0])
        lines.append(mem)
assert len(lines) == 640 and all(len(m) == 8 for m in lines)

point_lines = [[] for _ in range(512)]
for j, mem in enumerate(lines):
    for p in mem:
        point_lines[p].append(j)
assert all(len(pl) == 10 for pl in point_lines)

# GQ axioms: for a point x not on a line L there is exactly one point of L collinear with x
coll = []
for x in range(512):
    c = set()
    for j in point_lines[x]:
        c.update(lines[j])
    c.discard(x)
    assert len(c) == 70
    coll.append(c)
for j, mem in enumerate(lines):
    ms = set(mem)
    for x in range(512):
        if x in ms:
            continue
        assert len(coll[x] & ms) == 1, "GQ axiom fails"

seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
out = sys.argv[2] if len(sys.argv) > 2 else "g.edges"
rng = random.Random(seed)

# base edges: (base_u, base_v, voltage); points are 0..511, lines 512..1151
base = []
for p in range(512):
    for j in point_lines[p]:
        base.append((p, 512 + j, rng.choice([0, 2, 4])))
order = list(range(640))
rng.shuffle(order)
for i in range(640):
    a, b = order[i], order[(i + 1) % 640]
    base.append((512 + a, 512 + b, rng.choice([1, 3, 5])))

NB = 1152
n = 6 * NB
with open(out, "w") as f:
    f.write(f"{n}\n")
    for (u, v, g) in base:
        for h in range(6):
            f.write(f"{6 * u + h} {6 * v + (h + g) % 6}\n")
print(f"base vertices {NB}, base edges {len(base)}, lift n={n}, lift edges {6 * len(base)}, written {out}")
