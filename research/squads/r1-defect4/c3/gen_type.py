#!/usr/bin/env python3
"""Cycle-type split encoding for a bipartite (k,3,-4)-graph (k >= 5, n = k^2-k-1).

usage:
  gen_type.py k PARTS out.cnf [--nolex] [--both]     write the CNF for one cycle type, e.g. PARTS = 19 or 3,3,5,...
  gen_type.py --types k                     list cycle types of n passing the determinant test (stdout)

Cycle type: the point repeat graph R_X is 2-regular on n points (R_X[x][y] = c(x,y)-1, c = #common lines), so it is a
disjoint union of cycles of lengths m >= 3 and digons (m = 2, a double edge, c = 3). PARTS lists these lengths.

Soundness of the fixed R_X (symmetry breaking by point relabelling):
  Permuting the points (rows of N) preserves every property of the graph. Any valid graph has R_X of some cycle type
  lambda, so relabelling its points gives R_X = C_lambda, where C_lambda puts each cycle on a run of consecutive labels
  (canonical matrix below). Hence the instance is SAT for lambda iff a graph with R_X = C_lambda exists, and the full
  problem is UNSAT iff every cycle type is UNSAT.  (Unique k=5 graph: R_X is one 19-cycle.)

Constraints (all consequences of the definition, or sound symmetry breaking):
  (a) every point on k lines, every line through k points (row/column sums = k).
  (b) EXACT common-line counts: for points x<y, #{lines containing both} = 1 + C[x][y]. This is the identity
      N N^T = (k-1)I + J + R_X with R_X = C fixed (a consequence of the definition, since R_X is defined by it).
  (c) diameter 3 for lines: any two lines share a point (for points, (b) gives >= 1 common line).
      Bipartite diameter 3 <=> same-side vertices have a common neighbour.
  (d) line normalisation: point 0 is on lines 0..k-1 (lines are interchangeable, so this is a relabelling).
  (e) column lex order: columns (lines) X[.,0] >=lex X[.,1] >=lex ... (sorting lines lexicographically is a line
      relabelling). Compatible with (d): sorting puts the lines through point 0 (row 0 entry 1) first.
      Encoded with the standard one-sided auxiliary chain (sound: a satisfying chain exists iff the order holds).
  With --nolex, only (a)-(d) are used.
  --both (option, the stronger variant): the LINE repeat graph is fixed too, R_Y = C_lambda, instead of (d),(e) and
      (c). Sound: (i) spec_filter.py shows the characteristic polynomial of C_mu determines mu among all partitions
      of n, and spec(R_Y) = spec(R_X) (NN^T and N^T N are isospectral), so the line type is lambda; (ii) permuting the
      lines does not change R_X and permuting points does not change R_Y, so the points can be labelled for R_X = C_lambda
      and then the lines for R_Y = C_lambda independently. Exact line-pair counts: #{points on both} = 1 + C[l][m].
"""
import sys, math, itertools
from pysat.formula import CNF, IDPool
from pysat.card import CardEnc, EncType


def partitions_min2(n, maxpart=None):
    """Partitions of n into parts >= 2, non-increasing."""
    if maxpart is None:
        maxpart = n
    if n == 0:
        yield []
        return
    for p in range(min(n, maxpart), 1, -1):
        for rest in partitions_min2(n - p, p):
            yield [p] + rest


def repeat_matrix(parts):
    """Canonical R_X for a cycle type: each cycle on consecutive labels; digon (m=2) gets entry 2."""
    n = sum(parts)
    C = [[0] * n for _ in range(n)]
    off = 0
    for m in parts:
        if m == 2:
            C[off][off + 1] = C[off + 1][off] = 2
        else:
            for i in range(m):
                a, b = off + i, off + (i + 1) % m
                C[a][b] = C[b][a] = 1
        off += m
    return C


def det_bareiss(M):
    """Exact integer determinant (Bareiss)."""
    A = [row[:] for row in M]
    n = len(A)
    sign, prev = 1, 1
    for k in range(n - 1):
        if A[k][k] == 0:
            for i in range(k + 1, n):
                if A[i][k] != 0:
                    A[k], A[i] = A[i], A[k]
                    sign = -sign
                    break
            else:
                return 0
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                A[i][j] = (A[i][j] * A[k][k] - A[i][k] * A[k][j]) // prev
        prev = A[k][k]
    return sign * A[n - 1][n - 1]


def det_test(k, parts):
    """Necessary condition: det(NN^T) = det((k-1)I + J + R_X) must be a perfect square (N integer)."""
    n = k * k - k - 1
    C = repeat_matrix(parts)
    M = [[(k - 1) * (x == y) + 1 + C[x][y] for y in range(n)] for x in range(n)]
    d = det_bareiss(M)
    r = math.isqrt(d) if d >= 0 else -1
    return d, (d >= 0 and r * r == d)


def build(k, parts, lex=True, both=False):
    n = k * k - k - 1
    assert sum(parts) == n and all(m >= 2 for m in parts), (parts, n)
    C = repeat_matrix(parts)
    pool = IDPool()
    cnf = CNF()
    X = {(p, l): pool.id(('x', p, l)) for p in range(n) for l in range(n)}

    # (d) point 0 on lines 0..k-1  (not used with --both: then the line labels are fixed by R_Y)
    if not both:
        for l in range(n):
            cnf.append([X[0, l]] if l < k else [-X[0, l]])
    # (a) row and column sums
    for p in range(n):
        cnf.extend(CardEnc.equals([X[p, l] for l in range(n)], bound=k, vpool=pool,
                                  encoding=EncType.seqcounter).clauses)
    for l in range(n):
        cnf.extend(CardEnc.equals([X[p, l] for p in range(n)], bound=k, vpool=pool,
                                  encoding=EncType.seqcounter).clauses)
    # (b) exact common-line count for every pair of points: sum_l N[x,l] N[y,l] = 1 + C[x][y]
    for x, y in itertools.combinations(range(n), 2):
        zs = []
        for l in range(n):
            z = pool.id(('z', x, y, l))
            a, b = X[x, l], X[y, l]
            cnf.append([-z, a]); cnf.append([-z, b]); cnf.append([-a, -b, z])  # z <-> a & b
            zs.append(z)
        cnf.extend(CardEnc.equals(zs, bound=1 + C[x][y], vpool=pool, encoding=EncType.seqcounter).clauses)
    if both:
        # (b') exact common-point count for every pair of lines: sum_p N[p,l] N[p,m] = 1 + C[l][m]
        for l, m in itertools.combinations(range(n), 2):
            zs = []
            for p in range(n):
                z = pool.id(('w', l, m, p))
                a, b = X[p, l], X[p, m]
                cnf.append([-z, a]); cnf.append([-z, b]); cnf.append([-a, -b, z])
                zs.append(z)
            cnf.extend(CardEnc.equals(zs, bound=1 + C[l][m], vpool=pool, encoding=EncType.seqcounter).clauses)
    else:
        # (c) any two lines share a point
        for l, m in itertools.combinations(range(n), 2):
            ys = []
            for p in range(n):
                y = pool.id(('y', l, m, p))
                cnf.append([-y, X[p, l]]); cnf.append([-y, X[p, m]])
                ys.append(y)
            cnf.append(ys)
    # (e) columns lex-nonincreasing: col[l] >=lex col[l+1]  (one-sided chain, sound)
    if lex and not both:
        for l in range(n - 1):
            A = [X[p, l] for p in range(n)]
            B = [X[p, l + 1] for p in range(n)]
            e = None  # None means "true" (prefix equal so far)
            for i in range(n):
                cl = [A[i], -B[i]]          # prefix equal -> A_i >= B_i
                if e is not None:
                    cl = [-e] + cl
                cnf.append(cl)
                if i == n - 1:
                    break
                e2 = pool.id(('e', l, i))   # prefix equal up to i  ->  e2 (forced true when it is equal)
                base = [] if e is None else [-e]
                cnf.append(base + [-A[i], -B[i], e2])
                cnf.append(base + [A[i], B[i], e2])
                e = e2
    return cnf, X, pool


if __name__ == '__main__':
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    if sys.argv[1] == '--types':
        k = int(args[0])
        n = k * k - k - 1
        tot = ok = 0
        for parts in partitions_min2(n):
            tot += 1
            d, sq = det_test(k, parts)
            if sq:
                ok += 1
                print(','.join(map(str, parts)))
        print(f'# k={k} n={n} cycle types={tot} pass det test={ok}', file=sys.stderr)
    else:
        k = int(args[0])
        parts = [int(x) for x in args[1].split(',')]
        out = args[2]
        cnf, X, pool = build(k, parts, lex='--nolex' not in sys.argv, both='--both' in sys.argv)
        cnf.to_file(out)
        print(f'k={k} n={k*k-k-1} parts={parts} vars={cnf.nv} clauses={len(cnf.clauses)}')
