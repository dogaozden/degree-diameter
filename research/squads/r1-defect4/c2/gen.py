#!/usr/bin/env python3
"""Card c2 (squad r1-defect4): explicit repeat-graph CNF for a bipartite (k,3,-4)-graph, k >= 5.
usage: gen.py k out.cnf

Graph facts (k >= 5: k-regular, n = k^2-k-1 points and n lines, Prop. 3.1 of arXiv:1203.3588):
  diameter 3 <=> any two points share a line and any two lines share a point;
  c(x,y) = number of common lines of points x != y, R[x][y] = c(x,y)-1, every row of R sums to 2 (so c <= 3).
Encoding of the repeat structure:
  for every pair of points x<y, Z[x,y,w] = X[x,w] & X[y,w] and a full-equivalence unary counter over w, truncated at 4,
  gives ge1 = (c>=1), R2 = (c>=2), R3 = (c>=3); the constraint c <= 3 is the clause -(c>=4).
  So R2 + R3 = c - 1 exactly. Same for pairs of lines (over points).
  Per point x: sum_y (R2+R3)[x,y] = 2 (exact), per line the same.
  Links (redundant, implied by the definitions, sound): if x,y both lie on lines l,m then R2(x,y) and R2'(l,m).
Symmetry breaking (each is a relabelling argument, applied in this order):
  Normal form (baseline): point 0 on lines 0..k-1, line 0 through points 0..k-1.
  S1: point 1 is a repeat neighbour of point 0 sharing lines 0 and 1, i.e. X[1,1]. Pick any point p with a repeat
      neighbour y (exists: every point has repeat sum 2). Pick a common line of p,y as line 0 and a second one as
      line 1; make p = point 0 and y = point 1 (y is on line 0). The lines through p, labels 1..k-1, may be permuted.
  S2a (digon): if c(0,1) = 3 then line 2 is also common to points 0 and 1: X[1,2]. Lines 1..k-1 permuted again.
  S2b (no digon): otherwise point 0 has one more repeat neighbour z with c(0,z) = 2. Permuting {2..k-1} (points on
      line 0) and {k..n-1} (points off line 0) we can label z = 2 if z is on line 0, else z = k. So R2(0,2) or R2(0,k).
      The clause R3(0,1) or R2(0,2) or R2(0,k) covers both cases (the digon case has R3(0,1) = 1).
      Note: z cannot in general be forced to be point 2, since y and z need not share a line through point 0.
  Double lex: permutations of rows {k+1..n-1} (points) and columns {k..n-1} (lines) fix every label used above
      (0, 1, 2, k and lines 0..k-1 are untouched), so the lex-minimal matrix in the orbit still satisfies everything.
      Lex-min w.r.t. row-major reading implies adjacent rows (points) ascending and adjacent columns (lines) ascending.
"""
import sys, itertools
from pysat.formula import CNF, IDPool
from pysat.card import CardEnc, EncType

J = 4  # unary counters are truncated at 4 (we need to know c>=1, c>=2, c>=3 and exclude c>=4)

def build(k):
    n = k * k - k - 1
    pool = IDPool(); cnf = CNF()
    T = pool.id('TRUE'); cnf.append([T]); F = -T
    aux = itertools.count()
    def new():
        return pool.id(('aux', next(aux)))

    def AND(a, b):
        if a == F or b == F: return F
        if a == T: return b
        if b == T: return a
        g = new()
        cnf.extend([[-g, a], [-g, b], [g, -a, -b]])
        return g

    def OR(a, b):
        if a == T or b == T: return T
        if a == F: return b
        if b == F: return a
        r = new()
        cnf.extend([[-r, a, b], [r, -a], [r, -b]])
        return r

    def counter(lits):
        """prev[j] <-> (at least j of lits are true), for j = 0..J, full equivalence."""
        prev = [T] + [F] * J
        for x in lits:
            prev = [T] + [OR(prev[j], AND(x, prev[j - 1])) for j in range(1, J + 1)]
        return prev

    X = {(p, l): pool.id(('x', p, l)) for p in range(n) for l in range(n)}
    # normal form (baseline)
    for l in range(n):
        cnf.append([X[0, l]] if l < k else [-X[0, l]])
    for p in range(1, n):
        cnf.append([X[p, 0]] if p < k else [-X[p, 0]])
    # k-regularity
    for p in range(n):
        cnf.extend(CardEnc.equals([X[p, l] for l in range(n)], bound=k, vpool=pool, encoding=EncType.seqcounter).clauses)
    for l in range(n):
        cnf.extend(CardEnc.equals([X[p, l] for p in range(n)], bound=k, vpool=pool, encoding=EncType.seqcounter).clauses)

    def pair_info(elems, wits, lit):
        """For each pair a<b of elems: diameter (>=1 common witness), c<=3, and returns (R2, R3) literals."""
        info = {}
        for a, b in itertools.combinations(elems, 2):
            ge = counter([AND(lit(a, w), lit(b, w)) for w in wits])
            cnf.append([ge[1]])        # diameter: a and b share at least one
            cnf.append([-ge[4]])       # repeat sum is 2, so c(a,b) <= 3
            info[(a, b)] = (ge[2], ge[3])
        return info

    pt = pair_info(range(n), range(n), lambda x, w: X[x, w])   # points, witnesses = lines
    ln = pair_info(range(n), range(n), lambda l, p: X[p, l])   # lines, witnesses = points

    def repeat_two(info):
        """sum over partners of (R2 + R3) equals 2, for every element."""
        for e in range(n):
            lits = []
            for f in range(n):
                if f != e:
                    lits += list(info[(min(e, f), max(e, f))])
            cnf.extend(CardEnc.equals(lits, bound=2, vpool=pool, encoding=EncType.seqcounter).clauses)
    repeat_two(pt)
    repeat_two(ln)

    # links: points x,y on lines l,m  =>  R2(x,y) and R2'(l,m)  (the same four incidences; implied by the definitions)
    for x, y in itertools.combinations(range(n), 2):
        for l, m in itertools.combinations(range(n), 2):
            prem = [-X[x, l], -X[y, l], -X[x, m], -X[y, m]]
            cnf.append(prem + [pt[(x, y)][0]])
            cnf.append(prem + [ln[(l, m)][0]])

    # S1: point 0 and point 1 share lines 0 and 1
    cnf.append([X[1, 1]])
    # S2a: digon (c(0,1)=3): line 2 is the third common line
    cnf.append([-pt[(0, 1)][1], X[1, 2]])
    # S2b: no digon: point 0's other repeat neighbour is point 2 (on line 0) or point k (off line 0)
    cnf.append([pt[(0, 1)][1], pt[(0, 2)][0], pt[(0, k)][0]])

    # double lex on rows k+1..n-1 (points) and columns k..n-1 (lines), adjacent pairs, ascending
    def lex_leq(a, b):
        e = T  # e: all earlier positions equal
        for i in range(len(a)):
            cnf.append([-e, -a[i], b[i]])
            if i + 1 < len(a):
                e2 = new()
                cnf.extend([[-e, -a[i], -b[i], e2], [-e, a[i], b[i], e2]])
                e = e2
    rows = list(range(k + 1, n)); cols = list(range(k, n))
    for p, q in zip(rows, rows[1:]):
        lex_leq([X[p, l] for l in range(n)], [X[q, l] for l in range(n)])
    for l, m in zip(cols, cols[1:]):
        lex_leq([X[p, l] for p in range(n)], [X[p, m] for p in range(n)])
    return cnf

if __name__ == '__main__':
    k = int(sys.argv[1]); cnf = build(k); cnf.to_file(sys.argv[2])
    print(f'k={k} n={k*k-k-1} vars={cnf.nv} clauses={len(cnf.clauses)}')
