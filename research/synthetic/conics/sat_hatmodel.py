"""The hat model of research/plus2/sat_gadget.py, at conic-adapted frames.

Bulk fixed: the incidences of PG(2,q) away from the gadget; a hat point H_X lies on the q-1 lines through X other
than ell and AX; a hat line K_X holds the q-1 points of AX other than A and X.  Gadget free: every incidence between
{A, points of ell, hat points, Q_i} and {ell, lines through A, hat lines, M_j}.  Constraints: degree <= q+2, any two
points collinear, any two lines concurrent.  (Same model as sat_gadget.py; only the frame differs.)

Frame: conic x z = y^2, A = (0,1,0) (external), ell = A^perp (y = 0), Z = (1,0,0), Z' = (0,0,1) on the conic,
conjugate pairs (1,0,u), (1,0,-u).  Hat points at the marked points given on the command line:
  'Z', "Z'", and 'u' for the pair (1,0,u),(1,0,-u).
With --polar, the solution is also required to be self-polar (theta = conic polarity on old elements, H_X <-> K_{X'}
(X' the conjugate of X), Q_i <-> M_i), i.e. incidence variables are tied in theta-pairs.

Usage: python sat_hatmodel.py q nQ nM marks...    e.g.  python sat_hatmodel.py 7 1 1 Z 1 2
"""
import argparse
import itertools
import time

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Solver

from pg2 import PG2


def model(q, marks, nQ, nM, polar):
    Pi = PG2(q)
    F = Pi.F
    A = Pi.pt((0, 1, 0))
    ell = Pi.perp(A)
    hp = []
    for m in marks:
        if m == 'Z':
            hp.append(Pi.pt((1, 0, 0)))
        elif m == "Z'":
            hp.append(Pi.pt((0, 0, 1)))
        else:
            u = int(m)
            hp += [Pi.pt((1, 0, u)), Pi.pt((1, 0, F.neg(u)))]
    assert len(set(hp)) == len(hp)
    hl = list(hp)
    AX = {x: Pi.join(A, x) for x in Pi.pts_on[ell]}
    thruA = set(AX.values())
    PTS = [('p', p) for p in Pi.points] + [('H', x) for x in hp] + [('Q', i) for i in range(nQ)]
    LNS = [('l', L) for L in Pi.lines] + [('K', x) for x in hl] + [('M', i) for i in range(nM)]
    GP = {('p', A)} | {('p', x) for x in Pi.pts_on[ell]} | {v for v in PTS if v[0] in 'HQ'}
    GL = {('l', ell)} | {('l', L) for L in thruA} | {v for v in LNS if v[0] in 'KM'}
    pool = IDPool()

    def conj(x):
        return Pi.meet(Pi.perp(x), ell)

    def th_p(p):      # point -> line
        if p[0] == 'p':
            return ('l', Pi.perp(p[1]))
        if p[0] == 'H':
            return ('K', conj(p[1]))
        return ('M', p[1])

    def th_l(L):      # line -> point
        if L[0] == 'l':
            return ('p', Pi.perp(L[1]))
        if L[0] == 'K':
            return ('H', conj(L[1]))
        return ('Q', L[1])

    def var(p, L):
        if polar:
            a, b = (p, L), (th_l(L), th_p(p))
            return pool.id(min(a, b, key=repr))
        return pool.id((p, L))

    def inc(p, L):
        if p in GP and L in GL:
            return var(p, L)
        if p[0] == 'p' and L[0] == 'l':
            return p[1] in Pi.pts_on[L[1]]
        if p[0] == 'H' and L[0] == 'l':
            return p[1] in Pi.pts_on[L[1]]
        if p[0] == 'p' and L[0] == 'K':
            return p[1] in Pi.pts_on[AX[L[1]]]
        return False

    INC = {(p, L): inc(p, L) for p in PTS for L in LNS}
    if polar:
        for (p, L), v in INC.items():
            w = INC[(th_l(L), th_p(p))]
            assert (v is True) == (w is True) and (v is False) == (w is False), (p, L)
    cls = []

    def deg_le(vals):
        fixed = sum(v is True for v in vals)
        lits = [v for v in vals if not isinstance(v, bool)]
        k = q + 2 - fixed
        if k < 0:
            return False
        if len(lits) > k:
            cls.extend(CardEnc.atmost(lits=lits, bound=k, vpool=pool, encoding=EncType.seqcounter).clauses)
        return True

    for p in PTS:
        if not deg_le([INC[p, L] for L in LNS]):
            return None
    for L in LNS:
        if not deg_le([INC[p, L] for p in PTS]):
            return None

    def cover(u, v, middles, get):
        opts = []
        for w in middles:
            a, b = get(u, w), get(v, w)
            if a is False or b is False:
                continue
            if a is True and b is True:
                return True
            if a is True:
                opts.append(b)
            elif b is True:
                opts.append(a)
            else:
                z = pool.id(('and', a, b))
                cls.extend([[-z, a], [-z, b]])
                opts.append(z)
        if not opts:
            return False
        cls.append(opts)
        return True

    for u, v in itertools.combinations(PTS, 2):
        if not cover(u, v, LNS, lambda p, L: INC[p, L]):
            return None
    for u, v in itertools.combinations(LNS, 2):
        if not cover(u, v, PTS, lambda L, p: INC[p, L]):
            return None
    return cls, pool


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('q', type=int)
    ap.add_argument('nQ', type=int)
    ap.add_argument('nM', type=int)
    ap.add_argument('marks', nargs='+')
    ap.add_argument('--polar', action='store_true')
    a = ap.parse_args()
    t0 = time.time()
    m = model(a.q, a.marks, a.nQ, a.nM, a.polar)
    tag = f"q={a.q} marks={' '.join(a.marks)} Q={a.nQ} M={a.nM} polar={a.polar}"
    if m is None:
        print(tag, 'UNSAT (trivially)')
        return
    cls, pool = m
    with Solver(name='cadical153', bootstrap_with=cls) as s:
        r = s.solve()
    print(tag, 'SAT' if r else 'UNSAT', f'({time.time() - t0:.1f}s)', flush=True)


if __name__ == '__main__':
    main()
