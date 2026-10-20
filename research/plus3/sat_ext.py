"""SAT: extend PG(2,q) by kP new points and kL new lines, beyond the hat model.

Everything about the new vertices is free (all their incidences, old or new).  The plane
itself may change too: at most E of its (q^2+q+1)(q+1) flags may be deleted, and at most
ADD old point / old line non-incidences may be added.  Constraints: degree <= q+2, every two
points share a line, every two lines share a point (= bipartite diameter 3, no isolated
vertices).  This is the whole model: no frame, no hats, no fixed gadget.

Symmetry breaking (sound): new points are sorted (lex, non-increasing) by their incidence
vector with the OLD lines; new lines likewise by OLD points.  These keys are not changed by
permuting the other side's new vertices, so both sorts can be imposed at once.
--force-del additionally requires flag 0 to be deleted.  By flag-transitivity of PGL(3,q)
this is sound for "at least one deletion"; run E=0 separately for the rest.

Usage: python sat_ext.py q kP kL E ADD [--time T] [--force-del] [--solver NAME] [--save]
ADD = -1 means unbounded (degree only).
"""
import argparse
import json
import sys
import threading
import time
from pathlib import Path

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat import solvers

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / 'plus2'))
from construction import pg_plane, lib, default_frame, core_incidences  # noqa: E402


def lex_geq(xs, ys, pool, tag):
    """Clauses for xs >=_lex ys (True > False), xs, ys lists of literals."""
    cls = []
    prev = None  # literal: "equal so far"
    for j, (x, y) in enumerate(zip(xs, ys)):
        e = pool.id((tag, 'eq', j))
        # under eq-so-far, need x >= y
        if prev is None:
            cls.append([x, -y])
            # e <-> (x <-> y)
            cls += [[-e, -x, y], [-e, x, -y]]
            cls += [[e, x, y], [e, -x, -y]]
        else:
            cls.append([-prev, x, -y])
            cls += [[-e, prev], [-e, -x, y], [-e, x, -y]]
            cls += [[e, -prev, x, y], [e, -prev, -x, -y]]
        prev = e
    return cls


def build(q, kP, kL, E, ADD, force_del=False, sym=None, near=None, conc=None, copy=None,
          chg_config=False, maxdel=False):
    pts, lns = pg_plane(q)
    N = len(pts)
    pool = IDPool()
    P = list(range(N + kP))   # points: 0..N-1 old, N.. new
    L = list(range(N + kL))   # lines likewise
    INC = {}
    flags, nonflags = [], []
    for p in P:
        for l in L:
            if p >= N or l >= N:
                INC[p, l] = pool.id(('i', p, l))
            elif p in lns[l]:
                if E == 0:
                    INC[p, l] = True
                else:
                    INC[p, l] = pool.id(('i', p, l))
                    flags.append(INC[p, l])
            else:
                if ADD == 0:
                    INC[p, l] = False
                else:
                    INC[p, l] = pool.id(('i', p, l))
                    nonflags.append(INC[p, l])
    cls = []

    def atmost(lits, k):
        if k < 0:
            raise ValueError('infeasible')
        if len(lits) > k:
            cls.extend(CardEnc.atmost(lits=lits, bound=k, vpool=pool,
                                      encoding=EncType.seqcounter).clauses)

    d = q + 2
    for p in P:
        vals = [INC[p, l] for l in L]
        atmost([v for v in vals if not isinstance(v, bool)], d - sum(v is True for v in vals))
    for l in L:
        vals = [INC[p, l] for p in P]
        atmost([v for v in vals if not isinstance(v, bool)], d - sum(v is True for v in vals))
    # redundant (implied) coverage bound, Lemma 2 of plus3.tex: every new point h has
    # (a_h + d_h)(q+1) >= N - (added pairs on its lines) >= N - ADD; dually for new lines.
    tmax = max(ADD, 0) if ADD >= 0 else N
    need = max(0, -(-(N - tmax) // (q + 1)))
    for h in range(N, N + kP):
        lits = [INC[h, l] for l in L]
        cls.extend(CardEnc.atleast(lits=lits, bound=need, vpool=pool,
                                   encoding=EncType.seqcounter).clauses)
    for K in range(N, N + kL):
        lits = [INC[p, K] for p in P]
        cls.extend(CardEnc.atleast(lits=lits, bound=need, vpool=pool,
                                   encoding=EncType.seqcounter).clauses)
    if E > 0 and maxdel:
        # Sound pruning: a deleted flag (x,L) with spare degree at both x and L could be put
        # back (adding an edge never increases a distance), so WLOG x or L has degree q+2.
        sat = {}
        for side, items in (('p', range(N)), ('l', range(N))):
            for u in items:
                g = pool.id(('sat', side, u))
                lits = [INC[u, l] for l in L] if side == 'p' else [INC[p, u] for p in P]
                lits = [v for v in lits if not isinstance(v, bool)]
                fixed = (sum(1 for l in L if INC[u, l] is True) if side == 'p'
                         else sum(1 for p in P if INC[p, u] is True))
                for c in CardEnc.atleast(lits=lits, bound=q + 2 - fixed, vpool=pool,
                                         encoding=EncType.seqcounter).clauses:
                    cls.append(c + [-g])
                sat[side, u] = g
        for l in range(N):
            for x in lns[l]:
                cls.append([INC[x, l], sat['p', x], sat['l', l]])
    if E > 0:
        atmost([-f for f in flags], E)
        if force_del:
            cls.append([-flags[0]])
    if ADD > 0:
        atmost(nonflags, ADD)

    def pair(get, side, others):
        for i, u in enumerate(side):
            for v in side[i + 1:]:
                opts, done = [], False
                for w in others:
                    a, b = get(u, w), get(v, w)
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
                        cls.extend([[-z, a], [-z, b]])
                        opts.append(z)
                if done:
                    continue
                if not opts:
                    raise ValueError('infeasible pair')
                cls.append(opts)

    pair(lambda u, w: INC[u, w], P, L)
    pair(lambda u, w: INC[w, u], L, P)

    start = 0
    if near is not None:
        # neighbourhood of the +2 core: new points 0..4 = Q, H_s and new lines 0..4 = M, K_s
        # (default frame); their incidences may differ from the core in at most `near` places.
        assert kP >= 5 and kL >= 5 and sym is None and not force_del
        A_, ell_, P_, X_ = default_frame(pts, lns)
        rp, rl, rinc = core_incidences(pts, lns, q, A_, ell_, P_, X_, hats=4)
        def idx(v, base):
            return v[1] if v[0] in ('p', 'l') else base + (0 if len(v) == 1 else 1 + X_.index(v[1]))
        ref = {(idx(a, N), idx(b, N)) for a, b in rinc}
        diff = []
        for (p, l), v in INC.items():
            if isinstance(v, bool) or p >= N + 5 or l >= N + 5 or (p < N and l < N):
                continue
            diff.append(-v if (p, l) in ref else v)
        atmost(diff, near)
        for i in range(5, kP - 1):
            a = [INC[N + i, l] for l in range(N)]
            b = [INC[N + i + 1, l] for l in range(N)]
            cls.extend(lex_geq(a, b, pool, ('lexP', i)))
        return N, P, L, INC, cls
    if conc is not None:
        # r = conc is the largest number of old lines through one old point that any new point
        # lies on.  WLOG (PGL(3,q) is transitive on points and induces the 3-transitive PGL(2,q)
        # on each pencil) new point 0 attains it at old point 0, on the first min(r,3) lines
        # through point 0.  Cases r = 2..q+1 together with --sym A cover everything.
        assert sym is None and near is None and not force_del and conc >= 2
        pencil = [l for l in range(N) if 0 in lns[l]]
        for l in pencil[:min(conc, 3)]:
            cls.append([INC[N, l]])
        if conc > 3:
            lits = [-INC[N, l] for l in pencil]          # at most q+1-r lines of the pencil missing
            atmost(lits, q + 1 - conc)
        for h in range(N, N + kP):
            for x in range(N):
                atmost([INC[h, l] for l in range(N) if x in lns[l]], conc)
        start = 1
    lstart = 0
    if copy is not None:
        # Copy model (Theorem thm:copies of plus3.tex; a theorem for q >= 3max(p,l)+9+e, an
        # assumption below that).  New point h copies an old point X (cp): all but at most one
        # old line of h passes through X, and every line through X is an old line of h or is
        # copied by a new line through h.  Dually for new lines.  Copies are distinct.
        # WLOG new point 0 copies point 0, and new line 0 copies a fixed line through point 0
        # (copy='on') or a fixed line not through it (copy='off').
        assert sym is None and near is None and conc is None and not force_del
        cp = {(h, x): pool.id(('cp', h, x)) for h in range(N, N + kP) for x in range(N)}
        cl = {(K, l): pool.id(('cl', K, l)) for K in range(N, N + kL) for l in range(N)}
        for h in range(N, N + kP):
            cls.extend(CardEnc.equals(lits=[cp[h, x] for x in range(N)], bound=1, vpool=pool,
                                      encoding=EncType.seqcounter).clauses)
        for K in range(N, N + kL):
            cls.extend(CardEnc.equals(lits=[cl[K, l] for l in range(N)], bound=1, vpool=pool,
                                      encoding=EncType.seqcounter).clauses)
        for x in range(N):
            atmost([cp[h, x] for h in range(N, N + kP)], 1)
        for l in range(N):
            atmost([cl[K, l] for K in range(N, N + kL)], 1)

        def guarded_atmost1(guard, lits):
            for c in CardEnc.atmost(lits=lits, bound=1, vpool=pool,
                                    encoding=EncType.seqcounter).clauses:
                cls.append(c + [-guard])

        for h in range(N, N + kP):
            for x in range(N):
                g = cp[h, x]
                guarded_atmost1(g, [INC[h, l] for l in range(N) if x not in lns[l]])
                for l in range(N):
                    if x not in lns[l]:
                        continue
                    opts = [INC[h, l]]
                    for K in range(N, N + kL):
                        z = pool.id(('cpz', h, K, l))
                        cls.extend([[-z, cl[K, l]], [-z, INC[h, K]]])
                        opts.append(z)
                    cls.append([-g] + opts)
        for K in range(N, N + kL):
            for l in range(N):
                g = cl[K, l]
                guarded_atmost1(g, [INC[x, K] for x in range(N) if x not in lns[l]])
                for x in lns[l]:
                    opts = [INC[x, K]]
                    for h in range(N, N + kP):
                        z = pool.id(('clz', K, h, x))
                        cls.extend([[-z, cp[h, x]], [-z, INC[h, K]]])
                        opts.append(z)
                    cls.append([-g] + opts)
        cls.append([cp[N, 0]])
        on0 = [l for l in range(N) if 0 in lns[l]]
        off0 = [l for l in range(N) if 0 not in lns[l]]
        cls.append([cl[N, on0[0] if copy == 'on' else off0[0]]])
        if chg_config:
            # changes only between copied points and copied lines
            for x in range(N):
                for l in range(N):
                    v = INC[x, l]
                    if isinstance(v, bool):
                        continue
                    bad = v if x not in lns[l] else -v
                    cls.append([-bad] + [cp[h, x] for h in range(N, N + kP)])
                    cls.append([-bad] + [cl[K, l] for K in range(N, N + kL)])
        start, lstart = 1, 1
    if sym == 'A':      # no new point lies on two old lines
        for h in range(N, N + kP):
            atmost([INC[h, l] for l in range(N)], 1)
    elif sym == 'B':    # new point 0 lies on old lines 0 and 1 (2-transitivity on lines)
        assert not force_del
        cls.extend([[INC[N, 0]], [INC[N, 1]]])
        start = 1
    for i in range(start, kP - 1):
        a = [INC[N + i, l] for l in range(N)]
        b = [INC[N + i + 1, l] for l in range(N)]
        cls += lex_geq(a, b, pool, ('lexP', i))
    for i in range(lstart, kL - 1):
        a = [INC[p, N + i] for p in range(N)]
        b = [INC[p, N + i + 1] for p in range(N)]
        cls += lex_geq(a, b, pool, ('lexL', i))
    return N, P, L, INC, cls


def decode(N, P, L, INC, model):
    ms = {x for x in model if x > 0}
    ids_p = {p: i for i, p in enumerate(P)}
    off = len(P)
    edges = []
    for (p, l), v in INC.items():
        if v is True or (not isinstance(v, bool) and v in ms):
            edges.append((ids_p[p], off + l))
    return len(P) + len(L), edges


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('q', type=int)
    ap.add_argument('kP', type=int)
    ap.add_argument('kL', type=int)
    ap.add_argument('E', type=int)
    ap.add_argument('ADD', type=int)
    ap.add_argument('--time', type=float, default=600)
    ap.add_argument('--force-del', action='store_true')
    ap.add_argument('--solver', default='cadical153')
    ap.add_argument('--save', action='store_true')
    ap.add_argument('--maxdel', action='store_true', help='WLOG every deleted flag has a saturated end')
    ap.add_argument('--copy', choices=['on', 'off'], default=None,
                    help='copy model; new line 0 copies a line through (on) / not through (off) the point copied by new point 0')
    ap.add_argument('--chg-config', action='store_true', help='copy model: changes only between copied vertices')
    ap.add_argument('--conc', type=int, default=None,
                    help='case r of the concurrency split (see build); with --sym A covers all cases')
    ap.add_argument('--near', type=int, default=None,
                    help='only graphs whose first 5+5 new vertices differ from the +2 core in <= NEAR incidences')
    ap.add_argument('--sym', choices=['A', 'B'], default=None,
                    help='PG symmetry split: A = every new point on <= 1 old line; '
                         'B = new point 0 on old lines 0 and 1.  A and B together cover all cases.')
    a = ap.parse_args()
    t0 = time.time()
    tag = (f'q={a.q} kP={a.kP} kL={a.kL} E<={a.E} ADD<={a.ADD}'
           + (' force-del' if a.force_del else '') + (f' sym={a.sym}' if a.sym else '') + (f' near<={a.near}' if a.near is not None else '') + (f' conc={a.conc}' if a.conc else '') + (f' copy={a.copy}' if a.copy else '') + (' chg-config' if a.chg_config else '') + (' maxdel' if a.maxdel else '') + f' n={2*(a.q*a.q+a.q+1)+a.kP+a.kL}')
    try:
        N, P, L, INC, cls = build(a.q, a.kP, a.kL, a.E, a.ADD, a.force_del, a.sym, a.near, a.conc, a.copy, a.chg_config, a.maxdel)
    except ValueError as ex:
        print(tag, 'UNSAT (trivial:', ex, ')', flush=True)
        return
    nv = max(abs(x) for c in cls for x in c)
    s = solvers.Solver(name=a.solver, bootstrap_with=cls)
    timer = threading.Timer(a.time, s.interrupt)
    timer.start()
    res = s.solve_limited(expect_interrupt=True)
    timer.cancel()
    dt = time.time() - t0
    if res is None:
        print(tag, f'UNKNOWN (timeout {a.time:.0f}s; {nv} vars, {len(cls)} clauses)', flush=True)
    elif not res:
        print(tag, f'UNSAT ({dt:.1f}s; {nv} vars, {len(cls)} clauses)', flush=True)
    else:
        n, edges = decode(N, P, L, INC, s.get_model())
        ok = lib.is_valid(n, edges, a.q + 2, 3)
        lns, neg = pg_plane(a.q)[1], {-x for x in s.get_model() if x < 0}
        ne = sum(1 for (p, l), v in INC.items() if p < N and l < N and not isinstance(v, bool)
                 and p in lns[l] and v in neg)
        print(tag, f'SAT ({dt:.1f}s) valid={ok} deletions={ne}', flush=True)
        if a.save:
            out = HERE / 'graphs' / f'ext_q{a.q}_{a.kP}_{a.kL}_E{a.E}_A{a.ADD}{a.sym or ""}{"c" + str(a.conc) if a.conc else ""}{"copy" + a.copy if a.copy else ""}_n{n}.json'
            out.write_text(json.dumps({'case': f'd{a.q+2}D3', 'value': n, 'output': [n, edges]}))
            print('saved', out, flush=True)
    s.delete()


if __name__ == '__main__':
    main()
