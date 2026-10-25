#!/usr/bin/env python3
"""Bipartite graph of maximum degree 12 and diameter 5 on 11,664 vertices (thm-chartlift, Oct 24 2026; controller found by squad r3-chartlift card c2): route-chart lift of K3,3 + doubled matching over the metacyclic group Z_3 x|_2 Z_8 (order 24, m = 72), fibre F_3^4, 4 letters x 3 scalars; the chart r3/k4q3_diag_cls1.txt (16 singular patterns) covers both diagonals.
Self-contained (stdlib only).  Route-chart lift (CHART_LIFTS.md):
  * base: 4-regular bipartite multigraph on 3 + 3 vertices; base edge (a_i, b_j, colour c, voltage v);
  * controller: voltage lift by a group of order 24: (a_i, x) ~ (b_j, v * x); m = 72 vertices per side;
  * fibre F_3^4; controller edge of colour c lifts to ((a_i, x), u) ~ ((b_j, v*x), A_c u + lam b_c), lam in F_3.
Degree 4 x 3 = 12; order 2 * 72 * 81 = 11664.
F_3 elements are 0..2 with the tables below.  Vertex numbering: A-vertex ((a_i, x), u) -> (i*G + x)*81 + id(u);
B-vertex ((b_j, y), u) -> 5832 + (j*G + y)*81 + id(u); id(u) = sum u_t 3^t.
usage: python3 THIS out.edges   (apsp.c format: first line n, then one edge "u v" per line)"""
import sys, itertools
ADD = [[0, 1, 2], [1, 2, 0], [2, 0, 1]]
MUL = [[0, 0, 0], [0, 1, 2], [0, 2, 1]]
G = 24
T = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 1, 2, 3, 4, 5, 6, 7, 0, 17, 18, 19, 20, 21, 22, 23, 16, 9, 10, 11, 12, 13, 14, 15, 8, 2, 3, 4, 5, 6, 7, 0, 1, 10, 11, 12, 13, 14, 15, 8, 9, 18, 19, 20, 21, 22, 23, 16, 17, 3, 4, 5, 6, 7, 0, 1, 2, 19, 20, 21, 22, 23, 16, 17, 18, 11, 12, 13, 14, 15, 8, 9, 10, 4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19, 5, 6, 7, 0, 1, 2, 3, 4, 21, 22, 23, 16, 17, 18, 19, 20, 13, 14, 15, 8, 9, 10, 11, 12, 6, 7, 0, 1, 2, 3, 4, 5, 14, 15, 8, 9, 10, 11, 12, 13, 22, 23, 16, 17, 18, 19, 20, 21, 7, 0, 1, 2, 3, 4, 5, 6, 23, 16, 17, 18, 19, 20, 21, 22, 15, 8, 9, 10, 11, 12, 13, 14, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 8, 1, 2, 3, 4, 5, 6, 7, 0, 17, 18, 19, 20, 21, 22, 23, 16, 10, 11, 12, 13, 14, 15, 8, 9, 18, 19, 20, 21, 22, 23, 16, 17, 2, 3, 4, 5, 6, 7, 0, 1, 11, 12, 13, 14, 15, 8, 9, 10, 3, 4, 5, 6, 7, 0, 1, 2, 19, 20, 21, 22, 23, 16, 17, 18, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19, 4, 5, 6, 7, 0, 1, 2, 3, 13, 14, 15, 8, 9, 10, 11, 12, 5, 6, 7, 0, 1, 2, 3, 4, 21, 22, 23, 16, 17, 18, 19, 20, 14, 15, 8, 9, 10, 11, 12, 13, 22, 23, 16, 17, 18, 19, 20, 21, 6, 7, 0, 1, 2, 3, 4, 5, 15, 8, 9, 10, 11, 12, 13, 14, 7, 0, 1, 2, 3, 4, 5, 6, 23, 16, 17, 18, 19, 20, 21, 22, 16, 17, 18, 19, 20, 21, 22, 23, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22, 23, 16, 9, 10, 11, 12, 13, 14, 15, 8, 1, 2, 3, 4, 5, 6, 7, 0, 18, 19, 20, 21, 22, 23, 16, 17, 2, 3, 4, 5, 6, 7, 0, 1, 10, 11, 12, 13, 14, 15, 8, 9, 19, 20, 21, 22, 23, 16, 17, 18, 11, 12, 13, 14, 15, 8, 9, 10, 3, 4, 5, 6, 7, 0, 1, 2, 20, 21, 22, 23, 16, 17, 18, 19, 4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 21, 22, 23, 16, 17, 18, 19, 20, 13, 14, 15, 8, 9, 10, 11, 12, 5, 6, 7, 0, 1, 2, 3, 4, 22, 23, 16, 17, 18, 19, 20, 21, 6, 7, 0, 1, 2, 3, 4, 5, 14, 15, 8, 9, 10, 11, 12, 13, 23, 16, 17, 18, 19, 20, 21, 22, 15, 8, 9, 10, 11, 12, 13, 14, 7, 0, 1, 2, 3, 4, 5, 6]
def gmul(a, x): return T[a * G + x]
BASE = [(0, 0, 0, 0), (0, 0, 2, 22), (0, 1, 1, 0), (0, 2, 3, 0), (1, 1, 0, 18), (1, 1, 2, 16), (1, 0, 3, 0), (1, 2, 1, 11), (2, 2, 0, 16), (2, 2, 2, 4), (2, 0, 1, 0), (2, 1, 3, 23)]   # (i, j, colour, voltage)
A = [[[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]], [[0, 2, 2, 1], [0, 1, 0, 1], [2, 2, 2, 1], [1, 0, 2, 1]], [[1, 1, 2, 1], [1, 0, 2, 0], [0, 0, 1, 2], [1, 2, 0, 2]], [[1, 1, 2, 2], [0, 2, 1, 1], [2, 2, 0, 2], [0, 2, 1, 2]]]
B = [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]
q = 3; Q = q ** 4; R = 3

def mat_vec(M, v):
    out = []
    for row in M:
        s = 0
        for a, x in zip(row, v): s = ADD[s][MUL[a][x]]
        out.append(s)
    return out

def vid(v): return sum(c * q ** t for t, c in enumerate(v))

def build():
    m = R * G; nA = m * Q; E = []
    vecs = list(itertools.product(range(q), repeat=4))
    for (i, j, c, v) in BASE:
        for x in range(G):
            a, bb = i * G + x, j * G + gmul(v, x)
            for u in vecs:
                y0 = mat_vec(A[c], u)
                for lam in range(q):
                    y = [ADD[p][MUL[lam][t]] for p, t in zip(y0, B[c])]
                    E.append((a * Q + vid(u), nA + bb * Q + vid(y)))
    assert len(set(E)) == len(E), 'repeated edge'
    return 2 * nA, E

if __name__ == '__main__':
    n, E = build()
    with open(sys.argv[1], 'w') as f:
        f.write(f"{n}\n"); f.writelines(f"{a} {b}\n" for a, b in E)
    print('vertices', n, 'edges', len(E))
