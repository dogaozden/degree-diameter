#!/usr/bin/env python3
"""Bipartite graph of maximum degree 10 and diameter 5 on 4,032 vertices (thm-chartlift, Oct 24 2026; controller found by squad r2-chartlift card c4): route-chart lift of a Haar graph of Z_14 x|_9 Z_9 (order 126), fibre F_2^4, 5 letters x 2 scalars; the chart (charts/r2_k5_q2.txt, 230 singular patterns) covers both diagonals, so the controller needs no 4-cycles.
Self-contained (stdlib only).  Route-chart lift (research/theorems/CHART_LIFTS.md) of a Haar graph:
  * group G = Z_14 x|_9 Z_9: elements (x, y), (x1, y1)(x2, y2) = (x1 + 9^y1 x2 mod 14, y1 + y2 mod 9); order 126;
  * controller: Haar graph, a_g ~ b_(s g) for s = S[c], edge colour c (c = 0..4); 126 vertices per side;
  * fibre F_2^4; controller edge of colour c lifts to (a_g, u) ~ (b_(s g), A_c u + lam B_c), lam in F_2.
Degree 5 x 2 = 10; order 2 * 126 * 16 = 4032.
Vertex numbering: (a_g, u) -> idx(g)*16 + id(u), (b_h, u) -> 2016 + idx(h)*16 + id(u), idx(x, y) = x*9 + y,
id(u) = sum u_i 2^i.  F_2 elements are 0..1 with the tables below.
usage: python3 THIS out.edges   (apsp.c format: first line n, then one edge "u v" per line)"""
import sys, itertools
ADD = [[0, 1], [1, 0]]
MUL = [[0, 0], [0, 1]]
M, N, t = 14, 9, 9
S = [(0, 0), (5, 6), (13, 2), (8, 0), (10, 7)]   # S[c] = (x, y), the voltage of colour c
A = [[[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]], [[1, 1, 1, 0], [0, 0, 1, 0], [1, 1, 1, 1], [1, 0, 1, 1]], [[1, 1, 0, 0], [0, 1, 1, 0], [0, 1, 1, 1], [0, 0, 1, 1]], [[0, 1, 0, 1], [0, 1, 1, 1], [1, 0, 1, 0], [1, 1, 1, 0]], [[0, 1, 0, 0], [1, 0, 1, 0], [0, 0, 1, 1], [0, 1, 0, 1]]]
B = [[0, 0, 1, 1], [1, 0, 0, 1], [0, 1, 1, 0], [0, 1, 0, 1], [0, 1, 1, 1]]
q = 2; Q = q ** 4

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
