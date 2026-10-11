"""SAT search, looser family: kP new points and kL new lines with ALL their incidences free,
plus every PG(2,q) incidence between {A} u ell and {ell} u (lines through A) free.
Everything else is PG(2,q).  Constraints as in sat_gadget.py.

Usage: python sat_free.py q kP kL [seconds] [--ell2]
--ell2 also frees a second anti-flag (A2, ell2).
"""
import json
import sys
import threading
import time
from pathlib import Path

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Cadical153

sys.path.insert(0, str(Path(__file__).resolve().parent))
from construction import pg_plane, default_frame, lib  # noqa: E402


def build_model(q, kP, kL, second=False):
    points, lines = pg_plane(q)
    A, ell, P, _ = default_frame(points, lines)
    frames = [(A, ell)]
    if second:
        ell2 = next(j for j in range(len(lines)) if A not in lines[j] and j != ell)
        A2 = next(p for p in points if p not in lines[ell2] and p not in lines[ell] and p != A)
        frames.append((A2, ell2))
    GPs, GLs = set(), set()
    for a, l in frames:
        GPs |= {a} | set(lines[l])
        GLs |= {l} | {j for j in range(len(lines)) if a in lines[j]}
    PTS = [('p', p) for p in points] + [('N', i) for i in range(kP)]
    LNS = [('l', j) for j in range(len(lines))] + [('K', i) for i in range(kL)]
    pool = IDPool()
    INC = {}
    for p in PTS:
        for L in LNS:
            if p[0] == 'N' or L[0] == 'K':
                INC[p, L] = pool.id((p, L))
            elif p[1] in GPs and L[1] in GLs:
                INC[p, L] = pool.id((p, L))
            else:
                INC[p, L] = p[1] in lines[L[1]]
    clauses = []
    for is_pt, side, others in ((True, PTS, LNS), (False, LNS, PTS)):
        for u in side:
            vals = [INC[(u, w) if is_pt else (w, u)] for w in others]
            fixed = sum(v is True for v in vals)
            var = [v for v in vals if not isinstance(v, bool)]
            k = q + 2 - fixed
            if k < 0:
                return None
            if len(var) > k:
                clauses += CardEnc.atmost(lits=var, bound=k, vpool=pool,
                                          encoding=EncType.seqcounter).clauses
    for is_pt, side, others in ((True, PTS, LNS), (False, LNS, PTS)):
        for i, u in enumerate(side):
            for v in side[i + 1:]:
                opts, done = [], False
                for w in others:
                    a = INC[(u, w) if is_pt else (w, u)]
                    b = INC[(v, w) if is_pt else (w, v)]
                    if a is False or b is False:
                        continue
                    if a is True and b is True:
                        done = True
                        break
                    if a is True:
                        opts.append(b)
                    elif b is True:
                        opts.append(a)
                    else:
                        z = pool.id(('and', a, b))
                        clauses += [[-z, a], [-z, b]]
                        opts.append(z)
                if not done:
                    if not opts:
                        return None
                    clauses.append(opts)
    return PTS, LNS, INC, clauses, pool


def main():
    q, kP, kL = map(int, sys.argv[1:4])
    rest = [a for a in sys.argv[4:] if not a.startswith('--')]
    limit = float(rest[0]) if rest else 300
    second = '--ell2' in sys.argv
    t0 = time.time()
    m = build_model(q, kP, kL, second)
    n = 2 * (q * q + q + 1) + kP + kL
    tag = f'q={q} new points={kP} new lines={kL} n={n}' + (' (two frames)' if second else '')
    if m is None:
        print(tag, 'UNSAT (trivially)', flush=True)
        return
    PTS, LNS, INC, clauses, pool = m
    s = Cadical153(bootstrap_with=clauses)
    timer = threading.Timer(limit, s.interrupt)
    timer.start()
    res = s.solve_limited(expect_interrupt=True)
    timer.cancel()
    dt = time.time() - t0
    if res is None:
        print(tag, f'UNKNOWN (timeout {limit}s)', flush=True)
    elif not res:
        print(tag, f'UNSAT ({dt:.1f}s, {len(clauses)} clauses)', flush=True)
    else:
        ms = {x for x in s.get_model() if x > 0}
        ids = {v: i for i, v in enumerate(PTS + LNS)}
        edges = [(ids[p], ids[L]) for (p, L), v in INC.items()
                 if v is True or (not isinstance(v, bool) and v in ms)]
        ok = lib.is_valid(len(ids), edges, q + 2, 3)
        print(tag, f'SAT ({dt:.1f}s) valid={ok}', flush=True)
        out = Path(__file__).resolve().parent / 'graphs' / f'satfree_q{q}_{kP}_{kL}_n{len(ids)}.json'
        out.write_text(json.dumps({'case': f'd{q+2}D3', 'value': len(ids), 'output': [len(ids), edges]}))


if __name__ == '__main__':
    main()
