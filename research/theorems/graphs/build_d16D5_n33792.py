#!/usr/bin/env python3
"""Self-contained construction of a bipartite graph of maximum degree 16 and diameter 5 on 33,792 vertices
(beat-16-5-squad, Oct 24 2026).  No imports from the repo.

Construction (a route-chart lift of a voltage-lift controller):
  * Base: K_{3,3} plus a perfect matching (the matching edges doubled), vertices a0 a1 a2 | b0 b1 b2, 12 edges.
  * Controller: voltage lift of the base by Z_22.  A-vertex (a_i, g), B-vertex (b_j, h), g, h in Z_22; base edge
    e = (a_i, b_j, v_e) gives the controller edges (a_i, g) -- (b_j, g + v_e).  66 + 66 vertices, 4-regular, each edge
    carries the letter c_e of its base edge (a proper 4-edge-colouring).
  * Fibre F_4^4.  Lift vertex ((a_i, g), x) is joined to ((b_j, g + v_e), A_c x + lam * b_c) for lam in F_4,
    c = c_e.  Degree 4 * 4 = 16.  Order 2 * 66 * 256 = 33,792.
F_4 = {0, 1, w, w^2} is coded 0, 1, 2, 3 (a + b w -> a + 2b); addition is XOR.
usage: python3 build_d16D5_n33792.py out.edges   (apsp.c format: first line n, then one edge "u v" per line)
Vertex numbering: A-vertex ((a_i, g), x) -> (22 i + g) * 256 + id(x), B-vertex ((b_j, h), y) -> 16896 + (22 j + h) * 256
+ id(y), id(x) = x0 + 4 x1 + 16 x2 + 64 x3."""
import sys, itertools

MUL = [[0, 0, 0, 0], [0, 1, 2, 3], [0, 2, 3, 1], [0, 3, 1, 2]]
N = 22                      # Z_22
# base edges: (a_i, b_j, voltage in Z_22, chart letter)
BASE = [(0, 0, 0, 0), (0, 0, 15, 2), (0, 1, 0, 1), (0, 2, 0, 3),
        (1, 1, 7, 0), (1, 1, 3, 2), (1, 0, 0, 3), (1, 2, 19, 1),
        (2, 2, 6, 0), (2, 2, 17, 2), (2, 0, 0, 1), (2, 1, 8, 3)]
# chart: A_0..A_3 (rows), b_0..b_3
A = [[[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]],
     [[0, 1, 3, 0], [1, 0, 2, 3], [3, 2, 1, 3], [1, 2, 3, 1]],
     [[0, 1, 3, 2], [3, 0, 2, 3], [0, 3, 1, 2], [0, 1, 0, 3]],
     [[1, 0, 3, 3], [1, 0, 3, 0], [0, 0, 1, 1], [2, 3, 1, 2]]]
B = [(1, 2, 0, 2), (0, 1, 1, 2), (1, 0, 0, 2), (0, 1, 3, 2)]

def mat_vec(M, v):
    out = []
    for r in range(4):
        s = 0
        for c in range(4): s ^= MUL[M[r][c]][v[c]]
        out.append(s)
    return tuple(out)

def vid(v): return v[0] | (v[1] << 2) | (v[2] << 4) | (v[3] << 6)

def build():
    m = 3 * N; nA = m * 256; E = []
    vecs = list(itertools.product(range(4), repeat=4))
    for (i, j, v, c) in BASE:
        for g in range(N):
            a, b = i * N + g, j * N + (g + v) % N
            for x in vecs:
                y0 = mat_vec(A[c], x)
                for lam in range(4):
                    y = tuple(p ^ MUL[lam][q] for p, q in zip(y0, B[c]))
                    E.append((a * 256 + vid(x), nA + b * 256 + vid(y)))
    assert len(set(E)) == len(E), 'repeated edge'
    return 2 * nA, E

if __name__ == '__main__':
    n, E = build()
    with open(sys.argv[1], 'w') as f:
        f.write(f"{n}\n"); f.writelines(f"{u} {v}\n" for u, v in E)
    print('vertices', n, 'edges', len(E))
