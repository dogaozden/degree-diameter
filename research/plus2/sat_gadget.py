"""SAT search for bigger graphs inside the "hat" family.

Fixed part (the bulk): PG(2,q) incidences away from the gadget; each hat point H_X lies on the
q-1 lines through X other than ell and AX; each hat line K_X holds the q-1 points of AX other
than A and X.  Free part (the gadget): every incidence between a gadget point
{A, points of ell, H_X, Q_i} and a gadget line {ell, lines through A, K_X, M_j}.
Constraints: every degree <= q+2, every two points on a common line, every two lines through a
common point.  Then the incidence graph has max degree q+2 and diameter 3.

Run with a python that has python-sat (pysat), e.g. a scratch venv.
Usage: python sat_gadget.py q nHatPoints nHatLines nQ nM [seconds]
Hat points sit at the first nHatPoints points of ell other than P (P may be used if
nHatPoints = q+1), hat lines at the first nHatLines.
"""
import json
import sys
import time
from pathlib import Path

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Cadical153

sys.path.insert(0, str(Path(__file__).resolve().parent))
from construction import pg_plane, default_frame, line_through, lib  # noqa: E402


def model(q, kP, kL, nQ, nM):
    points, lines = pg_plane(q)
    A, ell, P, _ = default_frame(points, lines)
    on_ell = [P] + sorted(lines[ell] - {P})
    order = on_ell[1:] + [P]                       # hats prefer points other than P
    hp, hl = order[:kP], order[:kL]
    AX = {x: line_through(lines, A, x) for x in on_ell}
    thruA = set(AX.values())
    PTS = [('p', p) for p in points] + [('H', x) for x in hp] + [('Q', i) for i in range(nQ)]
    LNS = [('l', j) for j in range(len(lines))] + [('K', x) for x in hl] + [('M', i) for i in range(nM)]
    GP = {('p', A)} | {('p', x) for x in on_ell} | {v for v in PTS if v[0] in 'HQ'}
    GL = {('l', ell)} | {('l', j) for j in thruA} | {v for v in LNS if v[0] in 'KM'}
    pool = IDPool()

    def inc(p, L):
        """True, False, or a SAT variable."""
        if p in GP and L in GL:
            return pool.id((p, L))
        if p[0] == 'p' and L[0] == 'l':
            return p[1] in lines[L[1]]
        if p[0] == 'H' and L[0] == 'l':
            return p[1] in lines[L[1]]           # L not ell and not through A here
        if p[0] == 'p' and L[0] == 'K':
            return p[1] in lines[AX[L[1]]]       # p not A and not on ell here
        return False

    INC = {(p, L): inc(p, L) for p in PTS for L in LNS}
    clauses = []
    top = [0]

    def deg_le(lits_fixed, lits_var):
        k = q + 2 - lits_fixed
        if k < 0:
            return False
        if len(lits_var) > k:
            cnf = CardEnc.atmost(lits=lits_var, bound=k, vpool=pool, encoding=EncType.seqcounter)
            clauses.extend(cnf.clauses)
        return True

    for p in PTS:
        vals = [INC[p, L] for L in LNS]
        if not deg_le(sum(v is True for v in vals), [v for v in vals if not isinstance(v, bool)]):
            return None, 'degree overflow at ' + str(p)
    for L in LNS:
        vals = [INC[p, L] for p in PTS]
        if not deg_le(sum(v is True for v in vals), [v for v in vals if not isinstance(v, bool)]):
            return None, 'degree overflow at ' + str(L)

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
                clauses.extend([[-z, a], [-z, b]])
                opts.append(z)
        if not opts:
            return False
        clauses.append(opts)
        return True

    for i, u in enumerate(PTS):
        for v in PTS[i + 1:]:
            if not cover(u, v, LNS, lambda p, L: INC[p, L]):
                return None, f'points {u},{v} can never be collinear'
    for i, u in enumerate(LNS):
        for v in LNS[i + 1:]:
            if not cover(u, v, PTS, lambda L, p: INC[p, L]):
                return None, f'lines {u},{v} can never meet'
    return (PTS, LNS, INC, clauses, pool), 'ok'


def main():
    q, kP, kL, nQ, nM = map(int, sys.argv[1:6])
    limit = float(sys.argv[6]) if len(sys.argv) > 6 else 300
    t0 = time.time()
    m, msg = model(q, kP, kL, nQ, nM)
    n = 2 * (q * q + q + 1) + kP + kL + nQ + nM
    tag = f'q={q} hats(pts,lines)=({kP},{kL}) Q={nQ} M={nM} n={n}'
    if m is None:
        print(tag, 'UNSAT (trivially):', msg, flush=True)
        return
    PTS, LNS, INC, clauses, pool = m
    s = Cadical153(bootstrap_with=clauses)
    import threading
    timer = threading.Timer(limit, lambda: s.interrupt())
    timer.start()
    res = s.solve_limited(expect_interrupt=True)
    timer.cancel()
    dt = time.time() - t0
    if res is None:
        print(tag, f'UNKNOWN (timeout {limit}s)', flush=True)
        return
    if not res:
        print(tag, f'UNSAT ({dt:.1f}s, {len(clauses)} clauses)', flush=True)
        return
    model_set = {x for x in s.get_model() if x > 0}
    ids = {v: i for i, v in enumerate(PTS + LNS)}
    edges = []
    for (p, L), val in INC.items():
        if val is True or (not isinstance(val, bool) and val in model_set):
            edges.append((ids[p], ids[L]))
    nn = len(ids)
    ok = lib.is_valid(nn, edges, q + 2, 3)
    print(tag, f'SAT ({dt:.1f}s) graph valid={ok}', flush=True)
    out = Path(__file__).resolve().parent / 'graphs' / f'sat_q{q}_{kP}{kL}{nQ}{nM}_n{nn}.json'
    out.write_text(json.dumps({'case': f'd{q+2}D3', 'value': nn, 'output': [nn, edges]}))
    print('  saved', out)


if __name__ == '__main__':
    main()
