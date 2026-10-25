#!/usr/bin/env python3
"""Baseline CNF for a bipartite (k,3,-4)-graph, k >= 5 (then the graph is k-regular, Prop. 3.1 of arXiv:1203.3588,
so both sides have n = k^2-k-1 vertices). Diameter 3 <=> any two points share a line and any two lines share a point.
Normal form: point 0 is on lines 0..k-1, line 0 contains points 0..k-1.
usage: enc_d3m4.py k out.cnf"""
import sys, itertools
from pysat.formula import CNF, IDPool
from pysat.card import CardEnc, EncType

def build(k):
    n = k * k - k - 1
    pool = IDPool(); cnf = CNF()
    X = {(p, l): pool.id(('x', p, l)) for p in range(n) for l in range(n)}
    for l in range(n):
        cnf.append([X[0, l]] if l < k else [-X[0, l]])
    for p in range(1, n):
        cnf.append([X[p, 0]] if p < k else [-X[p, 0]])
    for p in range(n):
        cnf.extend(CardEnc.equals([X[p, l] for l in range(n)], bound=k, vpool=pool, encoding=EncType.seqcounter).clauses)
    for l in range(n):
        cnf.extend(CardEnc.equals([X[p, l] for p in range(n)], bound=k, vpool=pool, encoding=EncType.seqcounter).clauses)
    for side in (0, 1):
        E = (lambda u, w: X[u, w]) if side == 0 else (lambda u, w: X[w, u])
        for u, v in itertools.combinations(range(n), 2):
            ys = []
            for w in range(n):
                y = pool.id(('y', side, u, v, w))
                cnf.append([-y, E(u, w)]); cnf.append([-y, E(v, w)])
                ys.append(y)
            cnf.append(ys)
    return cnf

if __name__ == '__main__':
    k = int(sys.argv[1]); cnf = build(k); cnf.to_file(sys.argv[2])
    print(f'k={k} n={k*k-k-1} vars={cnf.nv} clauses={len(cnf.clauses)}')
