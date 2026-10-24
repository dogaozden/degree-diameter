#!/usr/bin/env python3
"""Write a self-contained builder script for a route-chart lift over F_3 whose controller is a voltage lift of a base
multigraph by a CYCLIC group Z_n (output of mlift_chart / mlift_joint3: "a b colour" lines, base edge e occupying
lines e*n .. e*n+n-1 with A-vertex i*n+g -> B-vertex j*n+(g+v_e) mod n).
usage: python3 make_builder.py BASE CTRL.edges CHART n OUT.py "<one-line provenance>"
The builder reproduces the lift exactly (same vertex numbering as gf3.py lift)."""
import sys

def main():
    base, ctrl, chart, n, out, prov = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]), sys.argv[5], sys.argv[6]
    toks = open(base).read().split(); k = int(toks[0])
    be = [(int(toks[1 + 2 * i]), int(toks[2 + 2 * i])) for i in range(4 * k)]
    rows = [tuple(map(int, l.split())) for l in open(ctrl) if l.strip()]
    assert len(rows) == 4 * k * n
    BASE = []
    for e, (i, j) in enumerate(be):
        a, b, c = rows[e * n]
        assert a == i * n and b // n == j
        v = b - j * n
        for x in range(n):                      # check the voltage is a cyclic shift
            assert rows[e * n + x] == (i * n + x, j * n + (x + v) % n, c), 'not a Z_n lift'
        BASE.append((i, j, v, c))
    ch = [list(map(int, l.split())) for l in open(chart) if l.strip()]
    A = [[ch[t][4 * r:4 * r + 4] for r in range(4)] for t in range(4)]
    B = [tuple(ch[4 + t]) for t in range(4)]
    m = k * n; N = 2 * 81 * m
    src = f'''#!/usr/bin/env python3
"""Self-contained construction of a bipartite graph of maximum degree 12 and diameter 5 on {N:,} vertices
({prov}).  No imports from the repo.

Construction (route-chart lift of a voltage-lift controller; research/squads/cells/d12D5.md):
  * Base: {k} + {k} vertices a_i | b_j, {4 * k} edges (list below).
  * Controller: voltage lift of the base by Z_{n}.  A-vertex (a_i, g), B-vertex (b_j, h), g, h in Z_{n}; base edge
    e = (a_i, b_j, v_e) gives the controller edges (a_i, g) -- (b_j, g + v_e).  {m} + {m} vertices, 4-regular, each
    edge carries the letter c_e of its base edge (a proper 4-edge-colouring).
  * Fibre F_3^4.  Lift vertex ((a_i, g), x) is joined to ((b_j, g + v_e), A_c x + lam * b_c) for lam in F_3,
    c = c_e.  Degree 4 * 3 = 12.  Order 2 * {m} * 81 = {N:,}.
usage: python3 THIS.py out.edges   (apsp.c format: first line n, then one edge "u v" per line)
Vertex numbering: A-vertex ((a_i, g), x) -> ({n} i + g) * 81 + id(x), B-vertex ((b_j, h), y) -> {81 * m} + ({n} j + h) * 81
+ id(y), id(x) = x0 + 3 x1 + 9 x2 + 27 x3."""
import sys, itertools

N = {n}                      # Z_{n}
K = {k}
# base edges: (a_i, b_j, voltage in Z_{n}, chart letter)
BASE = {BASE!r}
# chart over F_3: A_0..A_3 (rows), b_0..b_3
A = {A!r}
B = {B!r}

def mat_vec(M, v):
    return tuple(sum(M[r][c] * v[c] for c in range(4)) % 3 for r in range(4))

def vid(v): return v[0] + 3 * v[1] + 9 * v[2] + 27 * v[3]

def build():
    m = K * N; nA = m * 81; E = []
    vecs = list(itertools.product(range(3), repeat=4))
    for (i, j, v, c) in BASE:
        for g in range(N):
            a, b = i * N + g, j * N + (g + v) % N
            for x in vecs:
                y0 = mat_vec(A[c], x)
                for lam in range(3):
                    y = tuple((p + lam * q) % 3 for p, q in zip(y0, B[c]))
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
