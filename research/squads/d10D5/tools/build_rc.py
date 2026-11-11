#!/usr/bin/env python3
"""Independent builder for the Delta = 10 route-chart lift (job cell-10-5).  No imports from the repo.

usage: build_rc.py SOLUTION TABLE CHART OUT.edges
SOLUTION (ctrl5/ctrl6 output): first line "ctrl5 ..." or "ctrl6 ...", then per base edge either
    "i j voltage letter"                      (per-letter chart from CHART, offset 0), or
    "i j voltage letter offset"               (per-letter chart, offset c_e in GF(2)^4), or
    "i j voltage A0 A1 A2 A3 b c"             (per-edge chart: columns of A_e, b_e, offset c_e; CHART is ignored)
TABLE: group table "n" then n*n entries.  CHART: 5 lines "c0 c1 c2 c3 b" (columns of A_t, then b_t), ints 0..15.
Controller: (a_i, g) ~ (b_j, v*g).  Lift: ((a_i,g), x) ~ ((b_j, v*g), A x + c + lam*b), lam in {0,1}, x in GF(2)^4.
Vertex ids: A-vertex ((a_i,g),x) -> (i*n + g)*16 + x; B-vertex ((b_j,h),y) -> k*n*16 + (j*n + h)*16 + y.
OUT: apsp.c format (first line n, then "u v" per edge).  Repeated edges are reported and written once."""
import sys


def matvec(cols, x):
    y = 0
    for r in range(4):
        if x >> r & 1:
            y ^= cols[r]
    return y


def main():
    sol, tab, chartf, out = sys.argv[1:5]
    lines = [l.split() for l in open(sol) if l.strip()]
    head = lines[0]
    edges = [list(map(int, l)) for l in lines[1:]]
    T = [list(map(int, l.split())) for l in open(tab)][1:]
    n = len(T)
    chart = [list(map(int, l.split())) for l in open(chartf) if l.strip()] if chartf != '-' else None
    k = max(max(e[0], e[1]) for e in edges) + 1
    assert len(edges) == 5 * k, 'expected 5k base edges'
    nA = k * n * 16
    E = []
    for e in edges:
        i, j, v = e[0], e[1], e[2]
        if len(e) in (4, 5):
            t = e[3]; cols = chart[t][:4]; b = chart[t][4]; c = e[4] if len(e) == 5 else 0
        elif len(e) == 9:
            cols = e[3:7]; b = e[7]; c = e[8]
        else:
            raise SystemExit('bad edge line')
        for g in range(n):
            h = T[v][g]
            for x in range(16):
                y0 = matvec(cols, x) ^ c
                for lam in (0, 1):
                    y = y0 ^ (b if lam else 0)
                    E.append(((i * n + g) * 16 + x, nA + (j * n + h) * 16 + y))
    s = set(E)
    if len(s) != len(E):
        print('repeated edges:', len(E) - len(s))
    with open(out, 'w') as f:
        f.write(f"{2 * nA}\n")
        for u, w in sorted(s):
            f.write(f"{u} {w}\n")
    deg = {}
    for u, w in s:
        deg[u] = deg.get(u, 0) + 1; deg[w] = deg.get(w, 0) + 1
    print('vertices', 2 * nA, 'edges', len(s), 'max degree', max(deg.values()), 'min degree', min(deg.values()))


if __name__ == '__main__':
    main()
