"""SAT: self-polar extensions of PG(2,q), q odd, by k new points and k new lines.

theta0 is the polarity of the conic C: x z = y^2.  An extension is *self-polar* if theta0 extends to
a polarity theta of the new structure with theta(h_i) = K_i (the i-th new line).  Then
  * K_i contains the old point p  <=>  h_i lies on the old line p^perp,
  * h_i on K_j  <=>  h_j on K_i,
  * a flag (p, L) of PG(2,q) is deleted  <=>  (L^perp, p^perp) is deleted,
so only the points need to be constrained: degree <= q+2 and any two points collinear; the lines
follow by theta.  Optionally at most E flags of the plane are deleted (in theta-pairs), and at most
ADD non-incident old pairs are added (in theta-pairs).

A self-polar extension with k new points gives a graph of diameter 2 on q^2+q+1+k vertices with
maximum degree q+2 (fold by theta: p ~ p' iff p I theta(p')).

Symmetry breaking (sound): new points sorted lexicographically by their incidence vectors with the
old lines (theta preserves the form of the model under any permutation of the new points).
Optional --fixfirst: the first new point lies on the old line ell0 = (0,1,0)^perp (not sound in
general; reported separately).

Usage: python sat_polar.py q k [--E E] [--ADD A] [--time T]
"""
import argparse
import itertools
import json
import sys
import time

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Solver

from pg2 import PG2


def lex_geq(xs, ys, pool, tag):
    cls, prev = [], None
    for j, (x, y) in enumerate(zip(xs, ys)):
        e = pool.id((tag, 'eq', j))
        if prev is None:
            cls.append([x, -y])
            cls += [[-e, -x, y], [-e, x, -y], [e, x, y], [e, -x, -y]]
        else:
            cls.append([-prev, x, -y])
            cls += [[-e, prev], [-e, -x, y], [-e, x, -y], [e, -prev, x, y], [e, -prev, -x, -y]]
        prev = e
    return cls


def build(q, k, E, ADD):
    Pi = PG2(q)
    pts, lns = Pi.points, Pi.lines
    N = len(pts)
    pi = {p: i for i, p in enumerate(pts)}
    li = {L: i for i, L in enumerate(lns)}
    perp_pl = [li[Pi.perp(p)] for p in pts]          # point index -> line index
    perp_lp = [pi[Pi.perp(L)] for L in lns]          # line index -> point index
    pool = IDPool()
    cls = []
    x = [[pool.id(('x', i, L)) for L in range(N)] for i in range(k)]      # h_i on old line L
    y = {}
    for i in range(k):
        for j in range(i, k):
            y[(i, j)] = y[(j, i)] = pool.id(('y', i, j))                  # h_i on K_j (= h_j on K_i)

    # old incidence, with deletions/additions in theta-pairs
    inc = {}
    flagpair = {}
    for L in range(N):
        for p in Pi.pts_on[lns[L]]:
            a = pi[p]
            # flag (a, L) and its partner (perp(L), perp(a))
            b, M = perp_lp[L], perp_pl[a]
            key = min((a, L), (b, M))
            flagpair[(a, L)] = key
    nonflag = {}
    if E:
        for key in set(flagpair.values()):
            pool.id(('del', key))
    for a in range(N):
        for L in range(N):
            if (a, L) in flagpair:
                inc[(a, L)] = -pool.id(('del', flagpair[(a, L)])) if E else True
            else:
                if ADD:
                    b, M = perp_lp[L], perp_pl[a]
                    key = min((a, L), (b, M))
                    inc[(a, L)] = pool.id(('add', key))
                    nonflag[(a, L)] = key
                else:
                    inc[(a, L)] = False

    def lit_inc_old(a, L):
        return inc[(a, L)]

    # K_j contains old point a  <=>  h_j on perp(a)
    def lit_K(a, j):
        return x[j][perp_pl[a]]

    TRUE = pool.id('TRUE')
    cls.append([TRUE])

    def as_lit(v):
        if v is True:
            return TRUE
        if v is False:
            return -TRUE
        return v

    if E:
        dels = sorted({pool.id(('del', key)) for key in set(flagpair.values())})
        # count each theta-pair once (a self-paired flag counts once too): budget on pairs
        cls += CardEnc.atmost(dels, bound=E, vpool=pool, encoding=EncType.seqcounter).clauses
    if ADD:
        adds = sorted({pool.id(('add', key)) for key in set(nonflag.values())})
        cls += CardEnc.atmost(adds, bound=ADD, vpool=pool, encoding=EncType.seqcounter).clauses

    D = q + 2
    # degrees of old points: old lines kept/added + new lines K_j through it
    for a in range(N):
        lits = [as_lit(inc[(a, L)]) for L in range(N) if inc[(a, L)] is not False]
        lits += [lit_K(a, j) for j in range(k)]
        cls += CardEnc.atmost(lits, bound=D, vpool=pool, encoding=EncType.seqcounter).clauses
    # degrees of new points
    for i in range(k):
        lits = x[i] + [y[(i, j)] for j in range(k)]
        cls += CardEnc.atmost(lits, bound=D, vpool=pool, encoding=EncType.seqcounter).clauses

    def both(l1, l2, tag):
        l1, l2 = as_lit(l1), as_lit(l2)
        if l1 == -TRUE or l2 == -TRUE:
            return None
        if l1 == TRUE:
            return l2
        if l2 == TRUE:
            return l1
        z = pool.id(tag)
        cls.extend([[-z, l1], [-z, l2], [z, -l1, -l2]])
        return z

    # collinearity of points.  Lines: old L (point a on L is inc[(a,L)]; h_i on L is x[i][L]);
    # new K_j (old a on K_j is lit_K(a,j); h_i on K_j is y[(i,j)]).
    def on(P, line):
        kind, idx = line
        if P[0] == 'o':
            return inc[(P[1], idx)] if kind == 'o' else lit_K(P[1], idx)
        return x[P[1]][idx] if kind == 'o' else y[(P[1], idx)]

    allp = [('o', a) for a in range(N)] + [('n', i) for i in range(k)]
    alll = [('o', L) for L in range(N)] + [('n', j) for j in range(k)]
    for P1, P2 in itertools.combinations(allp, 2):
        if P1[0] == 'o' and P2[0] == 'o' and not E and not ADD:
            continue  # old pairs keep their line
        cl = []
        for line in alll:
            z = both(on(P1, line), on(P2, line), ('both', P1, P2, line))
            if z is None:
                continue
            cl.append(z)
            if z == TRUE:
                break
        cls.append(cl)
    # symmetry: new points sorted by old-line vectors
    for i in range(k - 1):
        cls += lex_geq(x[i], x[i + 1], pool, ('lex', i))
    return Pi, pts, lns, x, y, pool, cls, inc, perp_pl, perp_lp


def decode_and_check(model, q, k, Pi, pts, lns, x, y, pool, inc, perp_pl, perp_lp):
    ms = set(l for l in model if l > 0)
    N = len(pts)
    val = lambda v: (v is True) or (v is not False and v in ms)
    flags = set()
    for a in range(N):
        for L in range(N):
            if val(inc[(a, L)]):
                flags.add((('o', a), ('O', L)))
    for i in range(k):
        for L in range(N):
            if x[i][L] in ms:
                flags.add((('n', i), ('O', L)))
                flags.add((('o', perp_lp[L]), ('N', i)))
        for j in range(k):
            if y[(i, j)] in ms:
                flags.add((('n', i), ('N', j)))
    from pg2 import diameter3
    degP, degL = {}, {}
    for p, L in flags:
        degP[p] = degP.get(p, 0) + 1
        degL[L] = degL.get(L, 0) + 1
    return diameter3(flags), max(max(degP.values()), max(degL.values())), flags


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('q', type=int)
    ap.add_argument('k', type=int)
    ap.add_argument('--E', type=int, default=0)
    ap.add_argument('--ADD', type=int, default=0)
    ap.add_argument('--time', type=float, default=600)
    ap.add_argument('--solver', default='cadical153')
    ap.add_argument('--save', default=None)
    a = ap.parse_args()
    t0 = time.time()
    Pi, pts, lns, x, y, pool, cls, inc, perp_pl, perp_lp = build(a.q, a.k, a.E, a.ADD)
    print(f"q={a.q} k={a.k} E={a.E} ADD={a.ADD}: vars={pool.top} clauses={len(cls)} build {time.time()-t0:.1f}s",
          flush=True)
    import threading
    with Solver(name=a.solver, bootstrap_with=cls) as s:
        timer = threading.Timer(a.time, s.interrupt)
        timer.start()
        t1 = time.time()
        r = s.solve_limited(expect_interrupt=True)
        timer.cancel()
        dt = time.time() - t1
        if r is True:
            ok, md, flags = decode_and_check(s.get_model(), a.q, a.k, Pi, pts, lns, x, y, pool, inc, perp_pl, perp_lp)
            print(f"  SAT in {dt:.1f}s; decoded: diameter3={ok} maxdeg={md}")
            if a.save:
                json.dump(sorted([list(map(list, f)) for f in flags]), open(a.save, 'w'))
        elif r is False:
            print(f"  UNSAT in {dt:.1f}s")
        else:
            print(f"  UNKNOWN after {dt:.1f}s")


if __name__ == '__main__':
    main()
