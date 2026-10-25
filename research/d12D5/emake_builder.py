#!/usr/bin/env python3
"""Write a self-contained builder script for a route-chart lift over F_3 with a PER-EDGE chart (mlift_ejoint output:
controller lines "a b e", per-edge chart lines "A_e (16 entries row-major) b_e (4 entries)").  The controller edge list
is embedded verbatim, so any group works.
usage: python3 emake_builder.py BASE CTRL.edges ECHART OUT.py "<one-line provenance>" "<group description>" "<voltages>"
The builder reproduces the lift exactly (same vertex numbering as elift.py / gf3.py)."""
import sys

def main():
    base, ctrl, chart, out, prov, grp, volts = sys.argv[1:8]
    toks = open(base).read().split(); k = int(toks[0])
    be = [(int(toks[1 + 2 * i]), int(toks[2 + 2 * i])) for i in range(4 * k)]
    rows = [tuple(map(int, l.split())) for l in open(ctrl) if l.strip()]
    m = max(r[0] for r in rows) + 1; N = 2 * 81 * m
    ch = [list(map(int, l.split())) for l in open(chart) if l.strip()]
    LET = [([c[4 * r:4 * r + 4] for r in range(4)], tuple(c[16:20])) for c in ch]
    src = f'''#!/usr/bin/env python3
"""Self-contained construction of a bipartite graph of maximum degree 12 and diameter 5 on {N:,} vertices
({prov}).  No imports from the repo.

Construction (route-chart lift with a per-edge chart; research/d12D5/EDGECHART.md, research/squads/cells/d12D5.md):
  * Base: {k} + {k} vertices a_i | b_j, {4 * k} edges e = 0..{4 * k - 1}: {be!r}.
  * Controller: voltage lift of the base by {grp}, voltages {volts}; {m} + {m} vertices, 4-regular.  CTRL below lists
    its edges (A-vertex, B-vertex, base edge e).
  * Fibre F_3^4.  Every base edge e has its own letter (A_e, b_e) (LETTERS below).  Lift vertex (a, x) is joined to
    (b, A_e x + lam * b_e) for lam in F_3, for every controller edge (a, b, e).  Degree 4 * 3 = 12.
    Order 2 * {m} * 81 = {N:,}.
usage: python3 THIS.py out.edges   (apsp.c format: first line n, then one edge "u v" per line)
Vertex numbering: A-vertex (a, x) -> a * 81 + id(x), B-vertex (b, y) -> {81 * m} + b * 81 + id(y),
id(x) = x0 + 3 x1 + 9 x2 + 27 x3."""
import sys, itertools

M = {m}
CTRL = {rows!r}
# per base edge: (A_e as 4 rows, b_e)
LETTERS = {LET!r}

def mat_vec(A, v):
    return tuple(sum(A[r][c] * v[c] for c in range(4)) % 3 for r in range(4))

def vid(v): return v[0] + 3 * v[1] + 9 * v[2] + 27 * v[3]

def build():
    nA = M * 81; E = []
    vecs = list(itertools.product(range(3), repeat=4))
    assert len(CTRL) == 4 * M
    for (a, b, e) in CTRL:
        A, bv = LETTERS[e]
        for x in vecs:
            y0 = mat_vec(A, x)
            for lam in range(3):
                y = tuple((p + lam * q) % 3 for p, q in zip(y0, bv))
                E.append((a * 81 + vid(x), nA + b * 81 + vid(y)))
    assert len(set(E)) == len(E), 'repeated edge'
    return 2 * nA, E

if __name__ == '__main__':
    n, E = build()
    with open(sys.argv[1], 'w') as f:
        f.write(f"{{n}}\\n"); f.writelines(f"{{u}} {{v}}\\n" for u, v in E)
    print('vertices', n, 'edges', len(E))
'''
    open(out, 'w').write(src)
    print('wrote', out, 'for', N, 'vertices')

if __name__ == '__main__':
    main()
