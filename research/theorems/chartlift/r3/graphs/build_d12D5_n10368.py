#!/usr/bin/env python3
"""Bipartite graph of maximum degree 12 and diameter 5 on 10,368 vertices (thm-chartlift, Oct 24 2026): route-chart lift of a Haar graph of Z_16 x|_3 Z_4 (order 64), fibre F_3^4, 4 letters x 3 scalars; the chart (r3/k4q3_diag_tt.txt, 16 singular patterns) covers both diagonals, so the controller needs no 4-cycles.
Self-contained (stdlib only).  Route-chart lift (research/theorems/CHART_LIFTS.md) of a Haar graph:
  * group G = Z_16 x|_3 Z_4: elements (x, y), (x1, y1)(x2, y2) = (x1 + 3^y1 x2 mod 16, y1 + y2 mod 4); order 64;
  * controller: Haar graph, a_g ~ b_(s g) for s = S[c], edge colour c (c = 0..3); 64 vertices per side;
  * fibre F_3^4; controller edge of colour c lifts to (a_g, u) ~ (b_(s g), A_c u + lam B_c), lam in F_3.
Degree 4 x 3 = 12; order 2 * 64 * 81 = 10368.
Vertex numbering: (a_g, u) -> idx(g)*81 + id(u), (b_h, u) -> 5184 + idx(h)*81 + id(u), idx(x, y) = x*4 + y,
id(u) = sum u_i 3^i.  F_3 elements are 0..2 with the tables below.
usage: python3 THIS out.edges   (apsp.c format: first line n, then one edge "u v" per line)"""
import sys, itertools
ADD = [[0, 1, 2], [1, 2, 0], [2, 0, 1]]
MUL = [[0, 0, 0], [0, 1, 2], [0, 2, 1]]
M, N, t = 16, 4, 3
S = [(0, 0), (3, 1), (2, 3), (4, 3)]   # S[c] = (x, y), the voltage of colour c
A = [[[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]], [[0, 2, 2, 1], [0, 1, 0, 1], [2, 2, 2, 1], [1, 0, 2, 1]], [[0, 2, 2, 2], [2, 2, 2, 2], [0, 0, 1, 2], [2, 1, 0, 1]], [[1, 1, 1, 0], [2, 0, 2, 1], [2, 2, 0, 2], [0, 2, 1, 2]]]
B = [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]
q = 3; Q = q ** 4

def gmul(a, b): return ((a[0] + pow(t, a[1], M) * b[0]) % M, (a[1] + b[1]) % N)
def idx(a): return a[0] * N + a[1]

def mat_vec(Mx, v):
    out = []
    for row in Mx:
        s = 0
        for a, x in zip(row, v): s = ADD[s][MUL[a][x]]
        out.append(s)
    return out

def vid(v): return sum(c * q ** i for i, c in enumerate(v))

def build():
    G = [(x, y) for x in range(M) for y in range(N)]; nA = len(G) * Q; E = []
    vecs = list(itertools.product(range(q), repeat=4))
    for c, s in enumerate(S):
        for g in G:
            a, h = idx(g), idx(gmul(s, g))
            for u in vecs:
                y0 = mat_vec(A[c], u)
                for lam in range(q):
                    y = [ADD[p][MUL[lam][w]] for p, w in zip(y0, B[c])]
                    E.append((a * Q + vid(u), nA + h * Q + vid(y)))
    assert len(set(E)) == len(E), 'repeated edge'
    return 2 * nA, E

if __name__ == '__main__':
    n, E = build()
    with open(sys.argv[1], 'w') as f:
        f.write(f"{n}\n"); f.writelines(f"{a} {b}\n" for a, b in E)
    print('vertices', n, 'edges', len(E))
