"""SAT search one degree up: PG(2,q) plus new vertices at maximum degree q+3 (two spare links per old vertex).

Why: Delorme's 394 for (16,3) is PG(2,13) plus q+1 point clones on a conic and q+1 line clones on its tangents:
2(q^2+q+1) + 2(q+1) = 394 at q = 13. With two spare links per old line, at most two point clones share a line, so
pure clones stop at an arc (q+1 points, q odd). At one spare link the same count stops at 1 + 1, and
Araujo-Pardo-Lopez's hats beat it by 6 (our fourth hat by 8). This asks whether hats also exist one degree up.

Model: points of PG(2,q) plus kP new points, lines plus kL new lines. Incidences of new vertices are free. With
--gadget, every PG(2,q) incidence between {A} u ell and {ell} u (lines through A) is free too (the room that the
hats needed one degree down). With --clones, kP and kL include q+1 fixed point clones on a conic and q+1 fixed line
clones on its tangent lines (q odd), so only the extras are free. Constraints: degree <= q+3, every two points
collinear, every two lines concurrent; then the incidence graph has max degree q+3 and diameter 3 (checked again
with lib.is_valid on any model found).

Usage: python sat_q3.py q kP kL [seconds] [--gadget] [--clones]
Prints one line: SAT / UNSAT / UNKNOWN, and writes any graph found to graphs/satq3_*.json.
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


def conic_and_tangents(q, points, lines):
    """A conic of PG(2,q), q odd, as point ids, and its q+1 tangent lines as line ids (a dual conic)."""
    F = lib.GF(q)
    # Points are numbered in lib.projective_points order (see construction.pg_plane); the conic is x*z = y^2.
    coords = lib.projective_points(q)
    conic = [i for i, (x, y, z) in enumerate(coords) if F.add(F.mul(x, z), F.neg(F.mul(y, y))) == 0]
    assert len(conic) == q + 1, len(conic)
    cs = set(conic)
    tangents = [j for j, L in enumerate(lines) if len(cs & set(L)) == 1]
    assert len(tangents) == q + 1, len(tangents)
    return conic, tangents


def build_model(q, kP, kL, gadget=False, clones=False):
    points, lines = pg_plane(q)
    A, ell, P, _ = default_frame(points, lines)
    GPs, GLs = set(), set()
    if gadget:
        GPs = {A} | set(lines[ell])
        GLs = {ell} | {j for j in range(len(lines)) if A in lines[j]}
    fixedP, fixedL = {}, {}  # new point index -> old point it clones; new line index -> old line it clones
    if clones:
        conic, tangents = conic_and_tangents(q, points, lines)
        if kP < len(conic) or kL < len(tangents):
            raise SystemExit('with --clones, kP and kL must be at least q+1')
        fixedP = dict(enumerate(conic))
        fixedL = dict(enumerate(tangents))
    PTS = [('p', p) for p in points] + [('N', i) for i in range(kP)]
    LNS = [('l', j) for j in range(len(lines))] + [('K', i) for i in range(kL)]
    pool = IDPool()
    INC = {}
    for p in PTS:
        for L in LNS:
            if p[0] == 'N' and p[1] in fixedP and L[0] == 'l':
                INC[p, L] = fixedP[p[1]] in lines[L[1]]          # a fixed point clone: on every line of its pencil
            elif L[0] == 'K' and L[1] in fixedL and p[0] == 'p':
                INC[p, L] = p[1] in lines[fixedL[L[1]]]          # a fixed line clone: through every point of its line
            elif p[0] == 'N' or L[0] == 'K':
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
            k = q + 3 - fixed
            if k < 0:
                return None
            if len(var) > k:
                clauses += CardEnc.atmost(lits=var, bound=k, vpool=pool, encoding=EncType.seqcounter).clauses
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
    # Symmetry: free new points are interchangeable, so ask their incidence rows to be in a fixed order would be ideal;
    # a cheap partial break: the i-th free new point is on old line i or later (skipped; correctness first).
    return PTS, LNS, INC, clauses, pool


def main():
    q, kP, kL = map(int, sys.argv[1:4])
    rest = [a for a in sys.argv[4:] if not a.startswith('--')]
    limit = float(rest[0]) if rest else 300
    gadget, clones = '--gadget' in sys.argv, '--clones' in sys.argv
    t0 = time.time()
    m = build_model(q, kP, kL, gadget, clones)
    n = 2 * (q * q + q + 1) + kP + kL
    tag = f'deg q+3: q={q} new points={kP} new lines={kL} n={n}' + (' gadget' if gadget else '') + (' clones' if clones else '')
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
        print(tag, f'UNKNOWN (timeout {limit}s, {len(clauses)} clauses)', flush=True)
    elif not res:
        print(tag, f'UNSAT ({dt:.1f}s, {len(clauses)} clauses)', flush=True)
    else:
        ms = {x for x in s.get_model() if x > 0}
        ids = {v: i for i, v in enumerate(PTS + LNS)}
        edges = [(ids[p], ids[L]) for (p, L), v in INC.items() if v is True or (not isinstance(v, bool) and v in ms)]
        ok = lib.is_valid(len(ids), edges, q + 3, 3)
        print(tag, f'SAT ({dt:.1f}s) valid={ok}', flush=True)
        out = Path(__file__).resolve().parent / 'graphs' / f'satq3_q{q}_{kP}_{kL}_n{len(ids)}{"_g" if gadget else ""}.json'
        out.parent.mkdir(exist_ok=True)
        out.write_text(json.dumps({'case': f'd{q+3}D3', 'value': len(ids), 'output': [len(ids), edges]}))


if __name__ == '__main__':
    main()
