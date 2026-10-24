#!/usr/bin/env python3
"""Bipartite graph of maximum degree 8 and diameter 5 on 2,048 vertices (thm-chartlift, Oct 24 2026; controller found by squad r1-chartlift card c4): route-chart lift of K_{4,4} over Z_2 x Z_8, fibre F_2^4, 4 letters x 2 scalars.
Self-contained (stdlib only).  Route-chart lift (CHART_LIFTS.md):
  * base: 4-regular bipartite multigraph on 4 + 4 vertices; base edge (a_i, b_j, colour c, voltage v);
  * controller: voltage lift by a group of order 16: (a_i, x) ~ (b_j, v * x); m = 64 vertices per side;
  * fibre F_2^4; controller edge of colour c lifts to ((a_i, x), u) ~ ((b_j, v*x), A_c u + lam b_c), lam in F_2.
Degree 4 x 2 = 8; order 2 * 64 * 16 = 2048.
F_2 elements are 0..1 with the tables below.  Vertex numbering: A-vertex ((a_i, x), u) -> (i*G + x)*16 + id(u);
B-vertex ((b_j, y), u) -> 1024 + (j*G + y)*16 + id(u); id(u) = sum u_t 2^t.
usage: python3 THIS out.edges   (apsp.c format: first line n, then one edge "u v" per line)"""
import sys, itertools
ADD = [[0, 1], [1, 0]]
MUL = [[0, 0], [0, 1]]
G = 16
T = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 1, 2, 3, 4, 5, 6, 7, 0, 9, 10, 11, 12, 13, 14, 15, 8, 2, 3, 4, 5, 6, 7, 0, 1, 10, 11, 12, 13, 14, 15, 8, 9, 3, 4, 5, 6, 7, 0, 1, 2, 11, 12, 13, 14, 15, 8, 9, 10, 4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 5, 6, 7, 0, 1, 2, 3, 4, 13, 14, 15, 8, 9, 10, 11, 12, 6, 7, 0, 1, 2, 3, 4, 5, 14, 15, 8, 9, 10, 11, 12, 13, 7, 0, 1, 2, 3, 4, 5, 6, 15, 8, 9, 10, 11, 12, 13, 14, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 8, 1, 2, 3, 4, 5, 6, 7, 0, 10, 11, 12, 13, 14, 15, 8, 9, 2, 3, 4, 5, 6, 7, 0, 1, 11, 12, 13, 14, 15, 8, 9, 10, 3, 4, 5, 6, 7, 0, 1, 2, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3, 13, 14, 15, 8, 9, 10, 11, 12, 5, 6, 7, 0, 1, 2, 3, 4, 14, 15, 8, 9, 10, 11, 12, 13, 6, 7, 0, 1, 2, 3, 4, 5, 15, 8, 9, 10, 11, 12, 13, 14, 7, 0, 1, 2, 3, 4, 5, 6]
def gmul(a, x): return T[a * G + x]
BASE = [(0, 0, 3, 0), (0, 1, 2, 0), (0, 2, 1, 0), (0, 3, 0, 0), (1, 0, 1, 0), (1, 1, 3, 3), (1, 2, 0, 5), (1, 3, 2, 2), (2, 0, 2, 0), (2, 1, 0, 7), (2, 2, 3, 13), (2, 3, 1, 14), (3, 0, 0, 0), (3, 1, 1, 4), (3, 2, 2, 12), (3, 3, 3, 8)]   # (i, j, colour, voltage)
A = [[[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]], [[1, 1, 0, 1], [0, 0, 1, 1], [0, 1, 0, 1], [1, 0, 0, 1]], [[1, 1, 0, 0], [0, 0, 1, 0], [1, 0, 1, 1], [0, 0, 0, 1]], [[0, 0, 1, 0], [0, 0, 1, 1], [1, 1, 1, 1], [1, 0, 0, 1]]]
B = [[0, 0, 1, 0], [1, 0, 1, 1], [1, 1, 0, 0], [0, 1, 1, 1]]
q = 2; Q = q ** 4; R = 4

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
