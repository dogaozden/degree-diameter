#!/usr/bin/env python3
"""c7 (wildcard): CNF for a bipartite (k,3,-4)-graph, k >= 5, via DOUBLE-LEX on the residual incidence matrix.

Model: n = k^2-k-1 points (rows), n lines (columns), X[p][l] = 1 iff point p is on line l.
Diameter 3 <=> every two points share a line and every two lines share a point (pair coverage on both sides).
Row sums = column sums = k (k-regular for k >= 5, Prop. 3.1 of arXiv:1203.3588).

Symmetry breaking (the only idea new in this card; the rest is the baseline encoding):
  Relabelling points and lines independently preserves the problem, so we may assume
  (a) row 0 = 1^k 0^(n-k)   (point 0 on lines 0..k-1)           [same normal form as the baseline]
  (b) column 0 = 1^k 0^(n-k) (line 0 through points 0..k-1)      [same normal form as the baseline]
  (c) rows 1..n-1 are lex-non-increasing as full 0/1 vectors     [double-lex, rows]
  (d) columns 1..n-1 are lex-non-increasing as full vectors      [double-lex, columns]
Soundness of (a)-(d) together (proof sketch): start from any solution and fix (a),(b) by choosing the point-0 row and
line-0 column (any point p0 has k lines; relabel them 0..k-1; then relabel the points of line 0 as rows 0..k-1).
Then repeatedly (i) sort rows 1..n-1 lex-decreasing and (ii) sort columns 1..n-1 lex-decreasing.
  - (a) and (b) survive both sorts: row 0 and column 0 are the lex-maximal weight-k vectors, so they stay first, and
    columns with row-0 entry 1 stay in front of those with 0 (resp. rows with column-0 entry 1 stay in front).
  - Let Phi = row-major binary value of the matrix (row 0 most significant). Sorting rows 1..n-1 never decreases Phi.
    Sorting columns 1..n-1 never decreases Phi either: if the first changed row is r, the permutation preserves the
    prefix classes (rows < r) and then row r becomes the decreasing arrangement inside each class, so it grows.
  - Phi is bounded, so the process stops at a matrix satisfying (a)-(d).
The lex constraints are encoded with the standard one-directional chain (e_i = "prefixes equal so far"); the
e-variables are only forced true, so the encoding is satisfiable exactly when the lex inequality holds.

usage: gen.py k out.cnf [nosym]     ("nosym" drops (a)-(d); used only for soundness tests)
"""
import sys, itertools
from pysat.formula import CNF, IDPool
from pysat.card import CardEnc, EncType


def lex_geq(X, Y, pool, cnf, tag):
    """Add X >=_lex Y for equal-length lists of literals X, Y (index 0 most significant)."""
    e = None  # None encodes "true" (empty prefix)
    for i in range(len(X)):
        # prefix equal so far (e) implies X_i >= Y_i, i.e. not (X_i = 0 and Y_i = 1)
        cl = [X[i], -Y[i]] if e is None else [-e, X[i], -Y[i]]
        cnf.append(cl)
        if i == len(X) - 1:
            break
        f = pool.id(('lex', tag, i))
        base = [] if e is None else [-e]
        # e and X_i = Y_i  ->  f   (f is forced true when the prefix stays equal)
        cnf.append(base + [-X[i], -Y[i], f])
        cnf.append(base + [X[i], Y[i], f])
        e = f


def build(k, symbreak=True, n=None):
    if n is None:
        n = k * k - k - 1
    pool = IDPool()
    cnf = CNF()
    X = {(p, l): pool.id(('x', p, l)) for p in range(n) for l in range(n)}

    if symbreak:  # (a) row 0 and (b) column 0 normal form
        for l in range(n):
            cnf.append([X[0, l]] if l < k else [-X[0, l]])
        for p in range(1, n):
            cnf.append([X[p, 0]] if p < k else [-X[p, 0]])

    # row and column sums (every point on k lines, every line has k points)
    for p in range(n):
        cnf.extend(CardEnc.equals([X[p, l] for l in range(n)], bound=k, vpool=pool,
                                  encoding=EncType.seqcounter).clauses)
    for l in range(n):
        cnf.extend(CardEnc.equals([X[p, l] for p in range(n)], bound=k, vpool=pool,
                                  encoding=EncType.seqcounter).clauses)

    if symbreak:  # (c) rows 1..n-1 lex-non-increasing, (d) columns 1..n-1 lex-non-increasing
        for p in range(1, n - 1):
            lex_geq([X[p, l] for l in range(n)], [X[p + 1, l] for l in range(n)], pool, cnf, ('r', p))
        for l in range(1, n - 1):
            lex_geq([X[p, l] for p in range(n)], [X[p, l + 1] for p in range(n)], pool, cnf, ('c', l))

    # diameter-3 conditions: every two points share a line (side 0), every two lines share a point (side 1)
    for side in (0, 1):
        E = (lambda u, w: X[u, w]) if side == 0 else (lambda u, w: X[w, u])
        for u, v in itertools.combinations(range(n), 2):
            ys = []
            for w in range(n):
                y = pool.id(('y', side, u, v, w))
                cnf.append([-y, E(u, w)])
                cnf.append([-y, E(v, w)])
                ys.append(y)
            cnf.append(ys)
    return cnf


if __name__ == '__main__':
    k = int(sys.argv[1])
    sym = not (len(sys.argv) > 3 and sys.argv[3] == 'nosym')
    cnf = build(k, symbreak=sym)
    cnf.to_file(sys.argv[2])
    print(f'k={k} n={k*k-k-1} vars={cnf.nv} clauses={len(cnf.clauses)} symbreak={sym}')
