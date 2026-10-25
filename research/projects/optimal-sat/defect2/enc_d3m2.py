#!/usr/bin/env python3
"""CNF for a bipartite (k,3,-2)-graph in normal form.

Structure (proved in ../SUMMARY.md, Lemma 1): such a graph is k-regular with k(k-1) vertices per side, and its
vertices split into m = k(k-1)/2 disjoint 4-cycles. Label 4-cycle c as points 2c,2c+1 and lines 2c,2c+1.
Two points in different 4-cycles share exactly one line; the two points of a 4-cycle share only their own two
lines; dually for lines.

Normal form (Lemma 2): point 0 lies on lines 0,1 and 2i (i=1..k-2); point 1 on lines 0,1 and 2i+1 (i=1..k-2);
line 0 contains points 0,1 and 2j (j=k-1..2k-4); line 1 contains points 0,1 and 2j+1 (j=k-1..2k-4).

usage: enc_d3m2.py k out.cnf [--nosym]
"""
import sys
from pysat.formula import CNF, IDPool
from pysat.card import CardEnc, EncType

def build(k, sym=True):
    m = k * (k - 1) // 2
    n = 2 * m
    pool = IDPool()
    X = lambda p, l: pool.id(('x', p, l))
    cnf = CNF()
    for p in range(n):
        for l in range(n):
            X(p, l)
    unit = {}
    def fix(p, l, v):
        if (p, l) in unit:
            assert unit[(p, l)] == v, (p, l)
        unit[(p, l)] = v
    for c in range(m):
        for a in (0, 1):
            for b in (0, 1):
                fix(2 * c + a, 2 * c + b, 1)
    # normal form
    A = list(range(1, k - 1))          # 4-cycles of lines through points 0/1
    B = list(range(k - 1, 2 * k - 3))  # 4-cycles of points on lines 0/1
    for l in range(n):
        if l in (0, 1):
            continue
        c, b = divmod(l, 2)
        on0 = (c in A and b == 0)
        on1 = (c in A and b == 1)
        fix(0, l, 1 if on0 else 0)
        fix(1, l, 1 if on1 else 0)
    for p in range(n):
        if p in (0, 1):
            continue
        c, a = divmod(p, 2)
        on0 = (c in B and a == 0)
        on1 = (c in B and a == 1)
        if (p, 0) in unit:
            assert unit[(p, 0)] == (1 if on0 else 0)
        fix(p, 0, 1 if on0 else 0)
        fix(p, 1, 1 if on1 else 0)
    for (p, l), v in unit.items():
        cnf.append([X(p, l) if v else -X(p, l)])
    # degrees
    for p in range(n):
        lits = [X(p, l) for l in range(n)]
        cnf.extend(CardEnc.equals(lits, bound=k, vpool=pool, encoding=EncType.seqcounter).clauses)
    for l in range(n):
        lits = [X(p, l) for p in range(n)]
        cnf.extend(CardEnc.equals(lits, bound=k, vpool=pool, encoding=EncType.seqcounter).clauses)
    # pair conditions, both sides
    def pairs(side):
        E = (lambda u, w: X(u, w)) if side == 0 else (lambda u, w: X(w, u))
        for u in range(n):
            for v in range(u + 1, n):
                same = (u // 2 == v // 2)
                if same:
                    own = (2 * (u // 2), 2 * (u // 2) + 1)
                    for w in range(n):
                        if w in own:
                            continue
                        cnf.append([-E(u, w), -E(v, w)])
                else:
                    ys = []
                    for w in range(n):
                        y = pool.id(('y', side, u, v, w))
                        cnf.append([-y, E(u, w)])
                        cnf.append([-y, E(v, w)])
                        cnf.append([y, -E(u, w), -E(v, w)])
                        ys.append(y)
                    cnf.append(ys)
                    cnf.extend(CardEnc.atmost(ys, bound=1, vpool=pool, encoding=EncType.seqcounter).clauses)
    pairs(0)
    pairs(1)
    return cnf, pool, n

if __name__ == '__main__':
    k = int(sys.argv[1])
    cnf, pool, n = build(k)
    cnf.to_file(sys.argv[2])
    print(f'k={k} n={n} vars={cnf.nv} clauses={len(cnf.clauses)}')
