#!/usr/bin/env python3
"""The (6,5) 704-vertex graph as a cyclic Z88-lift of an 8-vertex base (deep-65b).
G = Z11 x M16 = Z88 :_45 Z2 (45 = 1 mod 11, 5 mod 8, 45^2 = 1 mod 88): (t, j)(s, l) = (t + 45^j s, j + l).
Its normal subgroup Z88 acts freely with 8 orbits, so the graph is a Z88-lift of the base on A0^j, A1^j, B0^j, B1^j
(j = 0, 1): for e = (s, l) in E1: A0^j -> B1^(j+l) with voltage 45^j s; for e in E2: B0^j -> A1^(j+l) with voltage
45^j s; A0^j - B0^j and A1^j - B1^j with voltage 0. Lift: (u, x) ~ (v, x + voltage).
Builds the edge list and compares it with records/d6D5_n704_split_c11xm16.edges up to the explicit relabelling
(a, i, j) <-> (t, j), t = CRT(a mod 11, i mod 8)."""
import sys
E1 = [(7, 5, 1), (9, 7, 0), (4, 4, 1), (6, 0, 0), (1, 1, 0)]
E2 = [(7, 1, 1), (8, 0, 1), (6, 1, 0), (9, 0, 1), (5, 4, 0)]
crt = lambda a, i: next(t for t in range(88) if t % 11 == a and t % 8 == i)
V = lambda e: (crt(e[0], e[1]), e[2])            # (s, l)
base = []                                         # (u, v, voltage), u on side A, v on side B; names like ('A0', j)
for j in (0, 1):
    base.append((('A0', j), ('B0', j), 0)); base.append((('A1', j), ('B1', j), 0))
    for e in E1: s, l = V(e); base.append((('A0', j), ('B1', (j + l) % 2), (45 ** j * s) % 88))
    for e in E2: s, l = V(e); base.append((('A1', (j + l) % 2), ('B0', j), (-(45 ** j * s)) % 88))   # B0^j -> A1^(j+l): reversed
print("base darts (A-vertex, B-vertex, Z88 voltage A->B):")
for b in base: print("  ", b)
# lift and compare with the record via the relabelling (fibre F, (a,i,j)) -> (F^j, t)
names = {'A0': 0, 'A1': 176, 'B0': 352, 'B1': 528}
def gid(t, j): a, i = t % 11, t % 8; return a * 16 + i * 2 + j     # index of (a, i, j) in the record numbering
E = set()
for (u, v, w) in base:
    for x in range(88):
        p = names[u[0]] + gid(x, u[1]); q = names[v[0]] + gid((x + w) % 88, v[1])
        E.add((min(p, q), max(p, q)))
f = open(sys.argv[1] if len(sys.argv) > 1 else 'd6D5_n704_split_c11xm16.edges').read().split()
R = {(min(int(f[k]), int(f[k + 1])), max(int(f[k]), int(f[k + 1]))) for k in range(1, len(f), 2)}
print("Z88-lift edges", len(E), "record edges", len(R), "identical:", E == R)
