#!/usr/bin/env python3
"""Find a (k,3,-2) graph with the naive normal-form encoding and print its 4-cycle quotient T (t_cd = number of
incidences between the points of 4-cycle c and the lines of 4-cycle d)."""
import sys
from pysat.solvers import Cadical153
from enc_d3m2 import build
k = int(sys.argv[1]); nsol = int(sys.argv[2]) if len(sys.argv) > 2 else 1
cnf, pool, n = build(k)
m = n // 2
s = Cadical153(bootstrap_with=cnf.clauses)
cnt = 0
while s.solve() and cnt < nsol:
    model = set(l for l in s.get_model() if l > 0)
    x = [[1 if pool.id(('x', p, l)) in model else 0 for l in range(n)] for p in range(n)]
    T = [[sum(x[p][l] for p in (2*c, 2*c+1) for l in (2*d, 2*d+1)) for d in range(m)] for c in range(m)]
    cnt += 1
    print('solution', cnt)
    for row in T: print(' '.join(map(str, row)))
    s.add_clause([-pool.id(('x', p, l)) for p in range(n) for l in range(n) if x[p][l]])
print('found', cnt)
