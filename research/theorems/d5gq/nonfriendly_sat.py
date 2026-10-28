"""Largest freed set R of a non-friendly transition (A = points, B = lines of the same GQ G, any bijection M: P -> L)
that is repaired inside the two levels, i.e. satisfies (E1)-(E3) of Theorem E.  SAT with a cardinality constraint.
usage: python3 nonfriendly_sat.py W|Q q k   -> is there (M, R) with |R| >= k ?"""
import sys, time
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType
from pysat.solvers import Cadical153
from gqlib import W, Q4
import numpy as np

which, q, k = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
G = W(q) if which == 'W' else Q4(q)
n = G.np; assert G.nl == n
P, L = range(n), range(n)
pool = IDPool()
m = lambda p, l: pool.id(('m', p, l))
r = lambda p: pool.id(('r', p))
z = lambda a, v: pool.id(('z', a, v))     # M(a) passes through point v
g = lambda a, l: pool.id(('g', a, l))     # M(a) concurrent with line l
w = lambda a, v: pool.id(('w', a, v))     # z & not r(a)
h = lambda a, l: pool.id(('h', a, l))     # g & not r(a)
cl = []
for p in P:
    cl.append([m(p, l) for l in L])
    cl += CardEnc.atmost([m(p, l) for l in L], 1, vpool=pool, encoding=EncType.seqcounter).clauses
for l in L:
    cl.append([m(p, l) for p in P])
    cl += CardEnc.atmost([m(p, l) for p in P], 1, vpool=pool, encoding=EncType.seqcounter).clauses
for a in P:
    for v in P:
        lits = [m(a, l) for l in G.plines[v]]          # z(a,v) <-> OR m(a,l), l through v
        cl.append([-z(a, v)] + lits)
        for x in lits: cl.append([z(a, v), -x])
        cl.append([-w(a, v), z(a, v)]); cl.append([-w(a, v), -r(a)]); cl.append([w(a, v), -z(a, v), r(a)])
    for l in L:
        lits = [m(a, l2) for l2 in np.nonzero(G.con[l])[0]]
        cl.append([-g(a, l)] + lits)
        for x in lits: cl.append([g(a, l), -x])
        cl.append([-h(a, l), g(a, l)]); cl.append([-h(a, l), -r(a)]); cl.append([h(a, l), -g(a, l), r(a)])
col = [np.nonzero(G.col[x])[0] for x in P]
for x in P:
    for v in P:   # (E2)
        cl.append([-r(x)] + [w(a, v) for a in col[x]])
    for l2 in L:  # (E3): if M(x) = l2, every line u has a point a not in R with M(a) concurrent with l2
        for u in L:
            cl.append([-r(x), -m(x, l2)] + [h(a, l2) for a in G.lines[u]])
for v in P:       # (E1): not all lines through v are images of freed points
    # some line l through v has M^-1(l) not in R:  OR_l OR_p (m(p,l) & ~r(p)); aux e(v,l)
    e = lambda l: pool.id(('e', l))
    cl.append([e(l) for l in G.plines[v]])
for l in L:
    e = pool.id(('e', l))
    # e(l) -> exists p: m(p,l) & ~r(p):  e(l) -> OR_p y(p,l), y(p,l) -> m(p,l), y(p,l) -> ~r(p)
    ys = []
    for p in P:
        y = pool.id(('y', p, l)); ys.append(y); cl.append([-y, m(p, l)]); cl.append([-y, -r(p)])
    cl.append([-e] + ys)
cl += CardEnc.atleast([r(p) for p in P], k, vpool=pool, encoding=EncType.seqcounter).clauses
# symmetry breaking (light): point 0 is freed
cl.append([r(0)])
t0 = time.time()
with Cadical153(bootstrap_with=cl) as s:
    ok = s.solve()
    print('%s(%d) k=%d: %s  (%.1fs, %d vars, %d clauses)' % (G.name, q, k, 'SAT' if ok else 'UNSAT', time.time() - t0, pool.top, len(cl)))
    if ok:
        mod = set(x for x in s.get_model() if x > 0)
        R = [p for p in P if r(p) in mod]
        M = [next(l for l in L if m(p, l) in mod) for p in P]
        print('R =', R); print('M =', M)
