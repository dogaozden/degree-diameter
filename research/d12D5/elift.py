#!/usr/bin/env python3
"""Lift of a controller with a PER-EDGE chart (mlift_ejoint.c output) over F_3^4.
Controller lines "a b e": A-vertex a, B-vertex b, base edge e.  Per-edge chart: line e = 16 entries of A_e (row-major)
then the 4 entries of b_e.  Lift: (a, x)_A -- (b, A_e x + lam b_e)_B, lam in F_3; 12-regular bipartite on 2*81*m vertices.
Vertex numbering as gf3.py: A-vertex (a, x) -> a*81 + id(x), B-vertex (b, y) -> 81 m + b*81 + id(y).
usage: python3 elift.py CONTROLLER ECHART OUT       (OUT: apsp.c edge list, first line n, then "u v")"""
import sys, itertools

def load_echart(fn):
    rows = [list(map(int, l.split())) for l in open(fn) if l.strip()]
    return [([[x % 3 for x in r[4 * i:4 * i + 4]] for i in range(4)], tuple(x % 3 for x in r[16:20])) for r in rows]

def vid(v):
    return v[0] + 3 * v[1] + 9 * v[2] + 27 * v[3]

def main(ctrl, chart, out):
    rows = [tuple(map(int, l.split())) for l in open(ctrl) if l.strip()]
    m = max(r[0] for r in rows) + 1
    assert len(rows) == 4 * m and max(r[1] for r in rows) + 1 == m
    C = load_echart(chart)
    vecs = list(itertools.product(range(3), repeat=4)); nA = m * 81
    E = []
    for a, bb, e in rows:
        A, b = C[e]
        for x in vecs:
            y0 = tuple(sum(A[r][c] * x[c] for c in range(4)) % 3 for r in range(4))
            for lam in range(3):
                y = tuple((p + lam * q) % 3 for p, q in zip(y0, b))
                E.append((a * 81 + vid(x), nA + bb * 81 + vid(y)))
    assert len(set(E)) == len(E), 'repeated edge'
    with open(out, 'w') as f:
        f.write(f"{2 * nA}\n"); f.writelines(f"{u} {v}\n" for u, v in E)
    print('controller m =', m, 'lift vertices', 2 * nA, 'edges', len(E))

if __name__ == '__main__':
    main(*sys.argv[1:4])
