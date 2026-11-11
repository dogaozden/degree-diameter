#!/usr/bin/env python3
"""Self-contained construction of a bipartite graph of maximum degree 12 and diameter 5 on 9,720 vertices
(K_{3,3} + matching over Z_20, joint chart/voltage annealing (mlift_joint3, seed 5)).  No imports from the repo.

Construction (route-chart lift of a voltage-lift controller; research/squads/cells/d12D5.md):
  * Base: 3 + 3 vertices a_i | b_j, 12 edges (list below).
  * Controller: voltage lift of the base by Z_20.  A-vertex (a_i, g), B-vertex (b_j, h), g, h in Z_20; base edge
    e = (a_i, b_j, v_e) gives the controller edges (a_i, g) -- (b_j, g + v_e).  60 + 60 vertices, 4-regular, each
    edge carries the letter c_e of its base edge (a proper 4-edge-colouring).
  * Fibre F_3^4.  Lift vertex ((a_i, g), x) is joined to ((b_j, g + v_e), A_c x + lam * b_c) for lam in F_3,
    c = c_e.  Degree 4 * 3 = 12.  Order 2 * 60 * 81 = 9,720.
usage: python3 THIS.py out.edges   (apsp.c format: first line n, then one edge "u v" per line)
Vertex numbering: A-vertex ((a_i, g), x) -> (20 i + g) * 81 + id(x), B-vertex ((b_j, h), y) -> 4860 + (20 j + h) * 81
+ id(y), id(x) = x0 + 3 x1 + 9 x2 + 27 x3."""
import sys, itertools

N = 20                      # Z_20
K = 3
# base edges: (a_i, b_j, voltage in Z_20, chart letter)
BASE = [(0, 0, 0, 0), (0, 0, 18, 1), (0, 1, 0, 2), (0, 2, 0, 3), (1, 1, 14, 0), (1, 1, 2, 1), (1, 0, 0, 3), (1, 2, 19, 2), (2, 2, 13, 0), (2, 2, 3, 1), (2, 0, 0, 2), (2, 1, 19, 3)]
# chart over F_3: A_0..A_3 (rows), b_0..b_3
A = [[[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]], [[1, 0, 0, 0], [0, 2, 0, 2], [2, 0, 0, 1], [2, 1, 1, 1]], [[1, 0, 0, 2], [1, 0, 2, 0], [2, 1, 0, 0], [2, 1, 1, 0]], [[1, 2, 0, 2], [1, 2, 0, 1], [2, 0, 2, 1], [1, 1, 1, 0]]]
B = [(0, 2, 0, 0), (2, 1, 2, 0), (2, 1, 1, 0), (2, 2, 1, 2)]

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
        f.write(f"{n}\n"); f.writelines(f"{u} {v}\n" for u, v in E)
    print('vertices', n, 'edges', len(E))
