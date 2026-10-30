#!/usr/bin/env python3
"""Write a bi-Cayley graph BiCay(G; R, L, S) (bicay.c) as a regular voltage lift of a 2+2 base by E (index-2 subgroup).

Vertices (g, i), g in G, i in {0,1}; edges (g,0)~(r g,0), (g,1)~(l g,1), (g,0)~(s g,1); colour par(g) xor i.
E acts freely by right multiplication with 4 orbits: a0 = (1,0)E, a1 = (t,1)E (colour 0), b0 = (t,0)E, b1 = (1,1)E
(colour 1), t = the first element of odd parity. Lift vertex (u, h) = (c x, i) with h = x^-1 (c the orbit
representative), so a base edge u -> u' with (s c = c' y, y in E) carries the voltage y^-1 (vl.c convention:
(a, h) ~ (b, h g)).
usage: bicay2lift.py BCGROUP "S ..." "R ..." "L ..." OUTBASE OUTGROUP
OUTBASE: vl base with voltages (vertex order a0 a1 b0 b1); OUTGROUP: multiplication table of E (identity first)."""
import sys

def main():
    gfile, Ss, Rs, Ls, obase, ogroup = sys.argv[1:7]
    tok = open(gfile).read().split()
    m = int(tok[0])
    mul = [list(map(int, tok[1 + i * m:1 + (i + 1) * m])) for i in range(m)]
    par = list(map(int, tok[1 + m * m:1 + m * m + m]))
    inv = [row.index(0) for row in mul]
    S, R, L = (list(map(int, x.split())) for x in (Ss, Rs, Ls))
    E = [g for g in range(m) if par[g] == 0]
    assert E[0] == 0
    idx = {g: k for k, g in enumerate(E)}
    t = next(g for g in range(m) if par[g] == 1)
    edges = []   # (u, w, voltage in E-index), u in {0 (a0), 1 (a1)}, w in {2 (b0), 3 (b1)}
    for r in R:   # a0 -> b0: r x = t (t^-1 r) x, y = t^-1 r
        y = mul[inv[t]][r]; edges.append((0, 2, idx[inv[y]]))
    for s in S:   # a0 -> b1: y = s
        edges.append((0, 3, idx[inv[s]]))
    for l in L:   # a1 -> b1: l t x, y = l t
        y = mul[l][t]; edges.append((1, 3, idx[inv[y]]))
    for s in S:   # a1 -> b0: (t x, 1) ~ (s^-1 t x, 0), s^-1 t = t y, y = t^-1 s^-1 t
        y = mul[mul[inv[t]][inv[s]]][t]; edges.append((1, 2, idx[inv[y]]))
    with open(obase, 'w') as f:
        f.write(f"4 {len(edges)}\n0 0 1 1\n")
        for u, w, g in edges: f.write(f"{u} {w} {g}\n")
    with open(ogroup, 'w') as f:
        f.write(f"{len(E)}\n")
        for a in E: f.write(" ".join(str(idx[mul[a][b]]) for b in E) + "\n")
    print(f"wrote {obase} ({len(edges)} edges) and {ogroup} (|E| = {len(E)}), t = {t}")

main()
