#!/usr/bin/env python3
"""Self-contained construction of a bipartite graph of maximum degree 12 and diameter 5 on 8,748 vertices
(job cell-12-5, Oct 24 2026).  No imports from the repo.

Construction (route-chart lift of a voltage-lift controller; the (16,5) construction of
research/theorems/BEAT_16_5_SQUAD.md with fibre F_3^4 instead of F_4^4, so 12 = 4 letters x 3 scalars):
  * Base: K_{3,3} plus a perfect matching (the matching edges doubled), vertices a0 a1 a2 | b0 b1 b2, 12 edges.
  * Controller: voltage lift of the base by Z_18.  A-vertex (a_i, g), B-vertex (b_j, h), g, h in Z_18; base edge
    e = (a_i, b_j, v_e) gives the controller edges (a_i, g) -- (b_j, g + v_e).  54 + 54 vertices, 4-regular, each edge
    carries the letter c_e of its base edge (a proper 4-edge-colouring).
  * Fibre F_3^4.  Lift vertex ((a_i, g), x) is joined to ((b_j, g + v_e), A_c x + lam * b_c) for lam in F_3,
    c = c_e.  Degree 4 * 3 = 12.  Order 2 * 54 * 81 = 8,748.
usage: python3 build_d12D5_n8748.py out.edges   (apsp.c format: first line n, then one edge "u v" per line)
Vertex numbering: A-vertex ((a_i, g), x) -> (18 i + g) * 81 + id(x), B-vertex ((b_j, h), y) -> 4374 + (18 j + h) * 81
+ id(y), id(x) = x0 + 3 x1 + 9 x2 + 27 x3."""
import sys, itertools

N = 18                      # Z_18
# base edges: (a_i, b_j, voltage in Z_18, chart letter)
BASE = [(0, 0, 0, 0), (0, 0, 9, 1), (0, 1, 0, 2), (0, 2, 0, 3),
        (1, 1, 17, 0), (1, 1, 12, 1), (1, 0, 0, 3), (1, 2, 7, 2),
        (2, 2, 10, 0), (2, 2, 6, 1), (2, 0, 0, 2), (2, 1, 16, 3)]
# chart over F_3: A_0..A_3 (rows), b_0..b_3
A = [[[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]],
     [[2, 2, 0, 0], [2, 2, 0, 1], [1, 0, 1, 1], [2, 2, 2, 1]],
     [[2, 0, 1, 1], [2, 2, 1, 0], [1, 1, 0, 0], [1, 2, 1, 0]],
     [[1, 1, 1, 0], [1, 2, 2, 2], [1, 2, 0, 2], [0, 0, 1, 2]]]
B = [(0, 0, 2, 1), (2, 1, 1, 1), (1, 2, 1, 1), (0, 2, 1, 1)]

def mat_vec(M, v):
    return tuple(sum(M[r][c] * v[c] for c in range(4)) % 3 for r in range(4))

def vid(v): return v[0] + 3 * v[1] + 9 * v[2] + 27 * v[3]

def build():
    m = 3 * N; nA = m * 81; E = []
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
