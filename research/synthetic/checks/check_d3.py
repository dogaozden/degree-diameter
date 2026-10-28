r"""Checks for Section 1 of SYNTHETIC.tex (diameter 3: the three hats of Araujo-Pardo--Lopez and
the four hats).

Both structures are built here from the coordinate-free rules of SYNTHETIC.tex, Section 1, on a
projective plane given only by its incidence relation (the code never looks at coordinates after
the plane is built).  Then every combinatorial claim of Section 1 is tested:

  * the result equals the coordinate construction of research/plus2/coords/coords.py (by_rules),
    for every admissible (a, c), q = 4, 5, 7 (and 8, 9);
  * the gadget tables (incidences among the special elements) printed in the note;
  * degrees and the counts of deficient elements;
  * the broken pairs (pairs of old points that stop being collinear, pairs of old lines that stop
    meeting) and the element that repairs each of them;
  * the needs of the new elements, case by case, with the repairing element named in the note;
  * any two points collinear, any two lines concurrent, diameter 3;
  * the list of changes from AL to the four hats (with the same a);
  * the duality: the dual of S(Pi; A, ell, X, sigma) is S(Pi^D; ell, A, lambda, sigma^-1);
  * the same in a non-Desarguesian plane of order 9 (Dickson nearfield plane), random frames.

Run:  python3 check_d3.py        (prints the gadget tables and 'ALL CHECKS PASSED')
"""
import itertools
import random
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[1] / 'plus2' / 'coords'))
import coords  # noqa: E402  (only for the comparison with the coordinate version, and GF)


# ------------------------------------------------------------------ an abstract projective plane

class Plane:
    """A projective plane given by its incidence relation only."""

    def __init__(self, points, lines, inc):
        self.points, self.lines = list(points), list(lines)
        self.inc = set(inc)
        self.pts_on = {L: set() for L in self.lines}
        self.lines_on = {p: set() for p in self.points}
        for p, L in self.inc:
            self.pts_on[L].add(p)
            self.lines_on[p].add(L)
        n = len(self.points)
        self.q = len(next(iter(self.pts_on.values()))) - 1
        assert n == len(self.lines) == self.q ** 2 + self.q + 1
        assert all(len(s) == self.q + 1 for s in self.pts_on.values())
        assert all(len(s) == self.q + 1 for s in self.lines_on.values())

    def join(self, p, r):
        (L,) = self.lines_on[p] & self.lines_on[r]
        return L

    def meet(self, L, N):
        (p,) = self.pts_on[L] & self.pts_on[N]
        return p

    def dual(self):
        return Plane(self.lines, self.points, {(L, p) for p, L in self.inc})


def pg2(q):
    fr = coords.Frame(q, 2)  # only used for its point and line lists
    F = fr.F
    inc = {(p, L) for p in fr.points for L in fr.lines if coords.dot(F, p[1], L[1]) == 0}
    return Plane(fr.points, fr.lines, inc)


def nearfield_plane9():
    """The plane of order 9 over the Dickson nearfield (x o m = xm if m is a square, x^3 m otherwise)."""
    q = 9
    F = coords.GF(q)
    squares = {F.mul(x, x) for x in range(1, q)}

    def nf(x, m):
        return F.mul(x, m) if (m == 0 or m in squares) else F.mul(F.mul(F.mul(x, x), x), m)

    assert any(nf(x, m) != nf(m, x) for x in range(q) for m in range(q))  # not a field
    pts = [('a', x, y) for x in range(q) for y in range(q)] + [('inf', m) for m in range(q)] + [('inf', 'v')]
    lines, inc = [], set()
    for m in range(q):
        for b in range(q):
            L = ('ln', m, b)
            lines.append(L)
            for x in range(q):
                inc.add((('a', x, F.add(nf(x, m), b)), L))
            inc.add((('inf', m), L))
    for c in range(q):
        L = ('vert', c)
        lines.append(L)
        for y in range(q):
            inc.add((('a', c, y), L))
        inc.add((('inf', 'v'), L))
    lines.append(('linf',))
    for m in list(range(q)) + ['v']:
        inc.add((('inf', m), ('linf',)))
    P = Plane(pts, lines, inc)
    for L, N in itertools.combinations(P.lines, 2):
        assert len(P.pts_on[L] & P.pts_on[N]) == 1
    return P


# ------------------------------------------------------------------ the two constructions, coordinate-free

def hats(Pi, A, ell, X, kind):
    """X: dict label -> point of ell.  kind 'AL': labels {0,1,a}; kind '4': labels {0,1,a,c}.
    Returns (incidence set, data).  New points ('Q',), ('H',s); new lines ('M',), ('K',s).
    Rules (SYNTHETIC.tex, Definitions 1.1 and 1.2):
      AL:  remove (X_a, lam_a); H_s on the lines through X_s other than ell; K_s through the points of
           lam_s other than A; M through the points of ell other than X_0, X_1, and the H_s; Q on the
           lines through A other than lam_0, lam_1, and the K_s; links A-K_a, H_a-ell, H_0-K_1, H_1-K_0.
      4:   remove the four flags (X_s, lam_s); add X_0-lam_c, X_c-lam_1, X_1-lam_0; H_s, K_s as above;
           M through the points of ell other than X_0, X_1, X_c, and the H_s; Q on the lines through A
           other than lam_0, lam_1, lam_c, and the K_s; links A-K_a, H_a-ell, H_0-K_c, H_c-K_1, H_1-K_0."""
    assert A not in Pi.pts_on[ell] and all(x in Pi.pts_on[ell] for x in X.values())
    S = list(X)
    lam = {s: Pi.join(A, X[s]) for s in S}
    if kind == 'AL':
        T = [0, 1]
        link = {0: 1, 1: 0}                 # the transposition (0 1)
        removed = [('a',)]
        rot = {}
    else:
        T = [0, 1, 'c']
        link = {0: 'c', 'c': 1, 1: 0}       # sigma = (0 c 1)
        removed = [(s,) for s in S]
        rot = link                          # X_t on lam_{sigma(t)}
    inc = set(Pi.inc)
    for (s,) in removed:
        inc.remove((X[s], lam[s]))
    for t, u in rot.items():
        inc.add((X[t], lam[u]))
    for s in S:
        for N in Pi.lines_on[X[s]] - {ell}:
            inc.add((('H', s), N))
        for p in Pi.pts_on[lam[s]] - {A}:
            inc.add((p, ('K', s)))
        inc.add((('H', s), ('M',)))
        inc.add((('Q',), ('K', s)))
    XT = {X[t] for t in T}
    for p in Pi.pts_on[ell] - XT:
        inc.add((p, ('M',)))
    lamT = {lam[t] for t in T}
    for N in Pi.lines_on[A] - lamT:
        inc.add((('Q',), N))
    inc.add((A, ('K', 'a')))
    inc.add((('H', 'a'), ell))
    for t in T:
        inc.add((('H', t), ('K', link[t])))
    data = dict(S=S, T=T, lam=lam, link=link, rot=rot, A=A, ell=ell, X=X)
    return inc, data


def structure(Pi, inc):
    pts = Pi.points + [('Q',)] + sorted({p for p, _ in inc if p[0] == 'H'}, key=str)
    lns = Pi.lines + [('M',)] + sorted({L for _, L in inc if L[0] == 'K'}, key=str)
    lines_on = {p: set() for p in pts}
    pts_on = {L: set() for L in lns}
    for p, L in inc:
        lines_on[p].add(L)
        pts_on[L].add(p)
    return pts, lns, lines_on, pts_on


def collinear(lines_on, u, v):
    return bool(lines_on[u] & lines_on[v])


def diameter(pts, lns, lines_on, pts_on):
    """Exact diameter of the incidence graph by BFS from every vertex."""
    nb = {}
    for p in pts:
        nb[('P', p)] = [('L', L) for L in lines_on[p]]
    for L in lns:
        nb[('L', L)] = [('P', p) for p in pts_on[L]]
    best = 0
    for v in nb:
        dist = {v: 0}
        frontier = [v]
        while frontier:
            nxt = []
            for x in frontier:
                for y in nb[x]:
                    if y not in dist:
                        dist[y] = dist[x] + 1
                        nxt.append(y)
            frontier = nxt
        if len(dist) < len(nb):
            return None
        best = max(best, max(dist.values()))
    return best


# ------------------------------------------------------------------ the checks

FAIL = []


def check(cond, msg):
    if not cond:
        FAIL.append(msg)
        print('FAIL:', msg)


def check_structure(Pi, A, ell, X, kind, verbose=False, full_diameter=True):
    q = Pi.q
    inc, d = hats(Pi, A, ell, X, kind)
    pts, lns, lines_on, pts_on = structure(Pi, inc)
    S, T, lam, link = d['S'], d['T'], d['lam'], d['link']
    H = {s: ('H', s) for s in S}
    K = {s: ('K', s) for s in S}
    Q, M = ('Q',), ('M',)
    nh = len(S)
    tag = f'{kind} q={q}'

    # counts
    check(len(pts) == len(lns) == q * q + q + 1 + nh + 1, f'{tag}: counts')

    # degrees: every element q+1 or q+2; the deficient elements as described
    ell_pts = Pi.pts_on[ell]
    pencil = Pi.lines_on[A]
    defic_p = {p for p in pts if len(lines_on[p]) == q + 1}
    defic_l = {L for L in lns if len(pts_on[L]) == q + 1}
    check(all(len(lines_on[p]) in (q + 1, q + 2) for p in pts), f'{tag}: point degrees')
    check(all(len(pts_on[L]) in (q + 1, q + 2) for L in lns), f'{tag}: line degrees')
    XS = {X[s] for s in S}
    lamS = {lam[s] for s in S}
    exp_p = {p for p in Pi.points if p != A and p not in ell_pts and Pi.meet(Pi.join(A, p), ell) not in XS}
    exp_l = {L for L in Pi.lines if L != ell and A not in Pi.pts_on[L] and Pi.join(A, Pi.meet(L, ell)) not in lamS}
    check(defic_p == exp_p, f'{tag}: deficient points = points off ell, A, on lines AY with Y not marked')
    check(defic_l == exp_l, f'{tag}: deficient lines (dual description)')
    nd = (q - 1) * (q - nh + 1)
    check(len(defic_p) == len(defic_l) == nd, f'{tag}: {nd} deficient points and lines')
    # a deficient point lies on exactly q - |S| deficient lines (regular completion argument)
    for p in defic_p:
        check(len(lines_on[p] & defic_l) == q - nh, f'{tag}: deficient point on q-|S| deficient lines')
    for L in defic_l:
        check(len(pts_on[L] & defic_p) == q - nh, f'{tag}: deficient line has q-|S| deficient points')

    # broken pairs: old pairs no longer joined by an OLD line (after removing flags and rotating)
    old_lines_on = {p: {L for L in lines_on[p] if L in Pi.pts_on} for p in Pi.points}
    old_pts_on = {L: {p for p in pts_on[L] if p in Pi.lines_on} for L in Pi.lines}
    broken_p = {frozenset((u, v)) for u, v in itertools.combinations(Pi.points, 2)
                if not (old_lines_on[u] & old_lines_on[v])}
    broken_l = {frozenset((L, N)) for L, N in itertools.combinations(Pi.lines, 2)
                if not (old_pts_on[L] & old_pts_on[N])}
    if kind == 'AL':
        exp_bp = {frozenset((X['a'], y)) for y in Pi.pts_on[lam['a']] - {X['a']}}
        exp_bl = {frozenset((lam['a'], N)) for N in Pi.lines_on[X['a']] - {lam['a']}}
    else:
        exp_bp = {frozenset((X[s], y)) for s in S for y in Pi.pts_on[lam[s]] - {X[s], A}} | {frozenset((X['a'], A))}
        exp_bl = {frozenset((lam[s], N)) for s in S for N in Pi.lines_on[X[s]] - {lam[s], ell}} | {frozenset((lam['a'], ell))}
    check(broken_p == exp_bp, f'{tag}: broken point pairs')
    check(broken_l == exp_bl, f'{tag}: broken line pairs')
    check(len(broken_p) == len(broken_l) == (q if kind == 'AL' else 4 * (q - 1) + 1), f'{tag}: number of broken pairs')
    # the repairs named in the note
    for pr in broken_p:
        u, v = tuple(pr)
        s = next(s for s in S if X[s] in pr)
        other = v if u == X[s] else u
        rep = K[s]  # K_s contains X_s and the points of lam_s other than A; K_a contains A by the link
        check(X[s] in pts_on[rep] and other in pts_on[rep], f'{tag}: repair of point pair by K_s')
    for pr in broken_l:
        L1, L2 = tuple(pr)
        s = next(s for s in S if lam[s] in pr)
        rep = H[s]
        check(lam[s] in lines_on[rep] and (L2 if L1 == lam[s] else L1) in lines_on[rep], f'{tag}: repair by H_s')
    # the rotation keeps X_t collinear with A, and lam_t concurrent with ell
    if kind == '4':
        for t in T:
            check(lam[link[t]] in lines_on[X[t]] and A in pts_on[lam[link[t]]], f'{tag}: X_t, A on lam_sigma(t)')
            inv = {v: k for k, v in link.items()}
            check(X[inv[t]] in pts_on[lam[t]] and X[inv[t]] in pts_on[ell], f'{tag}: lam_t meets ell in X_sigma^-1(t)')

    # pairs that the rotation makes doubly collinear (only a remark; recorded for the text)
    # needs of the new points, with the repairing element named in the note
    for u in Pi.points:
        # P2: Q and u
        if u == A:
            c = lam['a']
        elif u in ell_pts:
            if u in XS:
                c = K[next(s for s in S if X[s] == u)]
            else:
                c = Pi.join(A, u)
        else:
            Y = Pi.meet(Pi.join(A, u), ell)
            ts = [t for t in T if X[t] == Y]
            c = K[ts[0]] if ts else Pi.join(A, u)
        check(c in lines_on[u] and c in lines_on[Q], f'{tag}: Q and {u}')
        # P3: H_s and u
        for s in S:
            if u not in ell_pts:
                c = Pi.join(u, X[s])
            elif u == X[s]:
                c = next(N for N in Pi.lines_on[X[s]] if N not in (ell, lam[s]))
            elif u not in {X[t] for t in T}:
                c = M
            elif s == 'a':
                c = ell
            else:
                t = next(t for t in T if X[t] == u)
                if link[s] == t:
                    c = K[t]
                else:  # four hats only: t = sigma^-1(s), use lam_s
                    c = lam[s]
            check(c in lines_on[u] and c in lines_on[H[s]], f'{tag}: H_{s} and {u}')
    for s, s2 in itertools.combinations(S, 2):
        check(M in lines_on[H[s]] and M in lines_on[H[s2]], f'{tag}: H H via M')
    check(lam['a'] in lines_on[Q] and lam['a'] in lines_on[H['a']], f'{tag}: Q H_a via lam_a')
    for t in T:
        check(K[link[t]] in lines_on[Q] and K[link[t]] in lines_on[H[t]], f'{tag}: Q H_t via K_link(t)')

    # the points of ell and the lines through A are still matched by incidence (with H_a, K_a added)
    P_ell = pts_on[ell]
    L_A = lines_on[A]
    check(P_ell == set(Pi.pts_on[ell]) | {H['a']}, f'{tag}: points of ell = old ones and H_a')
    check(L_A == set(Pi.lines_on[A]) | {K['a']}, f'{tag}: lines through A = old ones and K_a')
    match = {(p, L) for p in P_ell for L in L_A if L in lines_on[p]}
    rho = d['rot'] if kind == '4' else {t: t for t in T}
    exp_match = ({(Y, Pi.join(A, Y)) for Y in Pi.pts_on[ell] if Y not in XS}
                 | {(X[t], lam[rho[t]]) for t in T} | {(X['a'], K['a']), (H['a'], lam['a'])})
    check(match == exp_match, f'{tag}: ell and the pencil at A are matched as described')

    # Observation 2 of [AL], sharpened: H_s is at the same distance from every element of Pi as X_s is
    # in Pi, except from X_s and (s != a) from ell; dually for K_s and lam_s (except lam_s and A)
    def bfs(src, lo, po):
        dist = {src: 0}
        fr = [src]
        while fr:
            nx = []
            for x in fr:
                for y in (lo[x] if x in lo else po[x]):
                    if y not in dist:
                        dist[y] = dist[x] + 1
                        nx.append(y)
            fr = nx
        return dist
    old = Pi.points + Pi.lines
    for s in S:
        dH, dX = bfs(H[s], lines_on, pts_on), bfs(X[s], Pi.lines_on, Pi.pts_on)
        check({y for y in old if dH[y] != dX[y]} == ({X[s], ell} if s != 'a' else {X[s]}), f'{tag}: H_s copies the distances of X_s')
        dK, dL = bfs(K[s], lines_on, pts_on), bfs(lam[s], Pi.lines_on, Pi.pts_on)
        check({y for y in old if dK[y] != dL[y]} == ({lam[s], A} if s != 'a' else {lam[s]}), f'{tag}: K_s copies the distances of lam_s')

    # global: any two points collinear, any two lines concurrent
    check(all(collinear(lines_on, u, v) for u, v in itertools.combinations(pts, 2)), f'{tag}: points collinear')
    check(all(pts_on[L] & pts_on[N] for L, N in itertools.combinations(lns, 2)), f'{tag}: lines concurrent')
    if full_diameter:
        check(diameter(pts, lns, lines_on, pts_on) == 3, f'{tag}: diameter 3')
    return inc, d, (pts, lns, lines_on, pts_on)


def gadget(Pi, inc, d):
    """Incidence matrix among the special elements (rows points, columns lines)."""
    S, lam, A, ell, X = d['S'], d['lam'], d['A'], d['ell'], d['X']
    order = [0, 'c', 1, 'a'] if 'c' in S else [0, 1, 'a']
    rows = [('A', A)] + [(f'X_{s}', X[s]) for s in order] + [('Q', ('Q',))] + [(f'H_{s}', ('H', s)) for s in order]
    cols = [('ell', ell)] + [(f'lam_{s}', lam[s]) for s in order] + [('M', ('M',))] + [(f'K_{s}', ('K', s)) for s in order]
    mat = {}
    for rn, r in rows:
        for cn, c in cols:
            if (r, c) in inc:
                mat[rn, cn] = 'x'
            elif (r, c) in Pi.inc:
                mat[rn, cn] = 'o'          # an incidence of the plane that was removed
            else:
                mat[rn, cn] = '.'
    return rows, cols, mat


def print_gadget(Pi, inc, d, title):
    rows, cols, mat = gadget(Pi, inc, d)
    print(title)
    print('        ' + ' '.join(f'{cn:>6s}' for cn, _ in cols))
    for rn, _ in rows:
        print(f'{rn:>7s} ' + ' '.join(f'{mat[rn, cn]:>6s}' for cn, _ in cols))
    print()
    return rows, cols, mat


def compare_with_coords(q, a, c=None):
    """Our coordinate-free build on PG(2,q) equals coords.by_rules (same element names)."""
    fr = coords.Frame(q, a, c)
    F = fr.F
    inc_pg = {(p, L) for p in fr.points for L in fr.lines if coords.dot(F, p[1], L[1]) == 0}
    Pi = Plane(fr.points, fr.lines, inc_pg)
    if c is None:
        X = {0: fr.X(0), 1: fr.X(1), 'a': fr.X(a)}
        kind = 'AL'
    else:
        X = {0: fr.X(0), 1: fr.X(1), 'a': fr.X(a), 'c': fr.X(c)}
        kind = '4'
    inc, d = hats(Pi, fr.A, fr.ell, X, kind)
    # rename labels a, c to the field elements used by coords.py
    ren = {'a': a, 'c': c, 0: 0, 1: 1}

    def rn(x):
        if isinstance(x, tuple) and x and x[0] in ('H', 'K'):
            return (x[0], ren[x[1]])
        return x
    inc = {(rn(p), rn(L)) for p, L in inc}
    ref = coords.by_rules(fr)
    check(inc == ref, f'coordinate-free {kind} build equals coords.by_rules, q={q}, a={a}, c={c}')
    return Pi, fr


def changes_AL_to_four(q, a, c):
    """Differences between AL(a) and the four hats (a, c), both on PG(2,q) with coords names."""
    fa = coords.Frame(q, a)
    f4 = coords.Frame(q, a, c)
    al, four = coords.by_rules(fa), coords.by_rules(f4)
    added, removed = four - al, al - four
    X, lam = f4.X, f4.lam
    H, K = (lambda s: ('H', s)), (lambda s: ('K', s))
    # H_c on the q lines through X_c other than ell, on M and on K_1; K_c through the q points of lam_c
    # other than A, through Q and through H_0
    F = f4.F
    lines_Xc = {f4.ln((w, 1, F.neg(c))) for w in f4.els}
    pts_lamc = {f4.pt((x, c, 1)) for x in f4.els}
    exp_added = ({(H(c), L) for L in lines_Xc} | {(H(c), ('M',)), (H(c), K(1))}
                 | {(p, K(c)) for p in pts_lamc} | {(('Q',), K(c)), (H(0), K(c))}
                 | {(X(0), lam(c)), (X(c), lam(1)), (X(1), lam(0))})
    exp_removed = {(X(0), lam(0)), (X(1), lam(1)), (X(c), lam(c)), (X(c), ('M',)), (('Q',), lam(c)), (H(0), K(1))}
    check(added == exp_added, f'AL -> 4 hats: added incidences, q={q}')
    check(removed == exp_removed, f'AL -> 4 hats: removed incidences, q={q}')
    check(len(added) - len(removed) == 2 * q + 1, f'AL -> 4 hats: 2q+1 more incidences, q={q}')


def check_duality(Pi, A, ell, X):
    """Dual of S(Pi; A, ell, X, sigma) = S(Pi^D; ell, A, lam, sigma^-1) via identity on Pi, H<->K, Q<->M."""
    inc, d = hats(Pi, A, ell, X, '4')
    lam = d['lam']
    D = Pi.dual()
    # in the dual plane: anti-flag (ell, A); marked 'points' lam_s on the 'line' A;
    # sigma^-1 = (0 1 c): relabel so that hats() (which always uses (0 c 1)) gives sigma^-1:
    # swap the labels 1 and c.
    Xd = {0: lam[0], 'c': lam[1], 1: lam['c'], 'a': lam['a']}
    incd, _ = hats(D, ell, A, Xd, '4')
    sw = {0: 0, 'a': 'a', 1: 'c', 'c': 1}

    def back(x):  # element of the dual construction -> element of the original
        if x == ('Q',):
            return ('M',)
        if x == ('M',):
            return ('Q',)
        if isinstance(x, tuple) and x and x[0] == 'H':
            return ('K', sw[x[1]])
        if isinstance(x, tuple) and x and x[0] == 'K':
            return ('H', sw[x[1]])
        return x
    dual_of_inc = {(back(L), back(p)) for p, L in incd}   # (dual point = line, dual line = point) -> (point, line)
    check(dual_of_inc == inc, 'duality of the four-hat structure (sigma -> sigma^-1)')
    # AL: self-dual with the transposition
    inc2, d2 = hats(Pi, A, ell, {k: X[k] for k in (0, 1, 'a')}, 'AL')
    Xd2 = {0: d2['lam'][0], 1: d2['lam'][1], 'a': d2['lam']['a']}
    incd2, _ = hats(D, ell, A, Xd2, 'AL')

    def back2(x):
        if x == ('Q',):
            return ('M',)
        if x == ('M',):
            return ('Q',)
        if isinstance(x, tuple) and x and x[0] in ('H', 'K'):
            return ('K' if x[0] == 'H' else 'H', x[1])
        return x
    check({(back2(L), back2(p)) for p, L in incd2} == inc2, 'duality of the AL structure')


def crossed_doubling(Pi, A, ell, X):
    """Double the frame set F = {A, ell} u {X_s, lam_s}: each x in F gets a copy x' (Q = A', M = ell',
    H_s = X_s', K_s = lam_s').  x' is incident with y' for y in F incident with x, and with every y
    outside F incident with x; the flags (X_s, lam_s) are crossed: X_s' - lam_s and X_s - lam_s'
    instead of X_s' - lam_s'.  No patches, no flag removed."""
    S = list(X)
    lam = {s: Pi.join(A, X[s]) for s in S}
    cp = {A: ('Q',), ell: ('M',)}
    for s in S:
        cp[X[s]] = ('H', s)
        cp[lam[s]] = ('K', s)
    Fset = set(cp)
    inc = set(Pi.inc)
    for p, L in Pi.inc:
        if p in Fset and L in Fset:
            s = next((s for s in S if (p, L) == (X[s], lam[s])), None)
            if s is None:
                inc.add((cp[p], cp[L]))
            else:
                inc.add((cp[p], L))
                inc.add((p, cp[L]))
        elif p in Fset:
            inc.add((cp[p], L))
        elif L in Fset:
            inc.add((p, cp[L]))
    return inc, lam


def check_doubling(Pi, A, ell, X, kind):
    """The structure = crossed doubling of the frame + patches - removed flags (+ rotation)."""
    q = Pi.q
    S = list(X)
    dbl, lam = crossed_doubling(Pi, A, ell, X)
    pts, lns, lines_on, pts_on = structure(Pi, dbl)
    H = {s: ('H', s) for s in S}
    K = {s: ('K', s) for s in S}
    Q, M = ('Q',), ('M',)
    # degrees in the doubling: q+1 at A, ell, Q, M, H_s, K_s (one spare slot each); X_s, lam_s at q+2
    spare = {A, Q} | set(H.values())
    spare_l = {ell, M} | set(K.values())
    for p in pts:
        dg = len(lines_on[p])
        check(dg <= q + 2, 'doubling: max degree')
        if p in spare:
            check(dg == q + 1, 'doubling: frame point with one spare slot')
        if p in X.values():
            check(dg == q + 2, 'doubling: X_s full')
    for L in lns:
        if L in spare_l:
            check(len(pts_on[L]) == q + 1, 'doubling: frame line with one spare slot')
        if L in lam.values():
            check(len(pts_on[L]) == q + 2, 'doubling: lam_s full')
    # far pairs (distance > 3): exactly (H_s, X_t), (K_s, lam_t) for s != t, (H_s, Q), (K_s, M)
    far_p = {frozenset((u, v)) for u, v in itertools.combinations(pts, 2) if not (lines_on[u] & lines_on[v])}
    far_l = {frozenset((L, N)) for L, N in itertools.combinations(lns, 2) if not (pts_on[L] & pts_on[N])}
    exp_p = {frozenset((H[s], X[t])) for s in S for t in S if s != t} | {frozenset((H[s], Q)) for s in S}
    exp_l = {frozenset((K[s], lam[t])) for s in S for t in S if s != t} | {frozenset((K[s], M)) for s in S}
    if len(S) == q + 1:   # every point of ell marked: also {Q, A} and {M, ell} (repaired by Q-lam_a, X_a-M)
        exp_p.add(frozenset((Q, A)))
        exp_l.add(frozenset((M, ell)))
    check(far_p == exp_p, f'doubling {kind} q={q}: far point pairs')
    check(far_l == exp_l, f'doubling {kind} q={q}: far line pairs')
    # points and lines are the only pairs that can be far for diameter 3 (Lemma: diam <= 3 iff these)
    # patches
    inc = set(dbl)
    if kind == 'AL':
        T, link = [0, 1], {0: 1, 1: 0}
        inc.remove((X['a'], lam['a']))
    else:
        T, link = [0, 1, 'c'], {0: 'c', 'c': 1, 1: 0}
        for s in S:
            inc.remove((X[s], lam[s]))
        for t in T:
            inc.add((X[t], lam[link[t]]))
    inc |= {(H[t], K[link[t]]) for t in T} | {(H['a'], ell), (A, K['a']), (X['a'], M), (Q, lam['a'])}
    ref, _ = hats(Pi, A, ell, X, kind)
    check(inc == ref, f'doubling {kind} q={q}: crossed doubling + patches = the construction')


def main():
    random.seed(7)
    # 0. the doubling viewpoint
    for q in (3, 4, 5, 7):
        Pi = pg2(q)
        for trial in range(4):
            ell = random.choice(Pi.lines)
            A = random.choice([p for p in Pi.points if p not in Pi.pts_on[ell]])
            on = random.sample(sorted(Pi.pts_on[ell], key=str), 4)
            check_doubling(Pi, A, ell, {0: on[0], 1: on[1], 'a': on[2]}, 'AL')
            check_doubling(Pi, A, ell, {0: on[0], 1: on[1], 'a': on[2], 'c': on[3]}, '4')
    print('crossed doubling + patches: checked for q = 3, 4, 5, 7')
    # 1. comparison with the coordinate version, every admissible (a, c)
    for q in (4, 5, 7, 8, 9):
        for a in range(2, q):
            compare_with_coords(q, a)
            for c in range(2, q):
                if c != a:
                    compare_with_coords(q, a, c)
                    if q in (4, 5, 7):
                        changes_AL_to_four(q, a, c)
    print('coordinate-free builds agree with coords.by_rules for q = 4, 5, 7, 8, 9, all (a, c)')

    # 2. all combinatorial claims, q = 4, 5, 7 (several frames each), and q = 3 for AL
    for q in (3, 4, 5, 7):
        Pi = pg2(q)
        frames = 0
        for trial in range(6 if q > 3 else 3):
            ell = random.choice(Pi.lines)
            A = random.choice([p for p in Pi.points if p not in Pi.pts_on[ell]])
            on = random.sample(sorted(Pi.pts_on[ell], key=str), 4 if q >= 3 else 3)
            XAL = {0: on[0], 1: on[1], 'a': on[2]}
            check_structure(Pi, A, ell, XAL, 'AL')
            X4 = {0: on[0], 1: on[1], 'a': on[2], 'c': on[3]}
            check_structure(Pi, A, ell, X4, '4')
            check_duality(Pi, A, ell, X4)
            frames += 1
        print(f'q = {q}: {frames} random frames, all claims checked (AL and four hats)')

    # 3. a non-Desarguesian plane of order 9
    Pi = nearfield_plane9()
    for trial in range(4):
        ell = random.choice(Pi.lines)
        A = random.choice([p for p in Pi.points if p not in Pi.pts_on[ell]])
        on = random.sample(sorted(Pi.pts_on[ell], key=str), 4)
        check_structure(Pi, A, ell, {0: on[0], 1: on[1], 'a': on[2]}, 'AL', full_diameter=(trial == 0))
        check_structure(Pi, A, ell, {0: on[0], 1: on[1], 'a': on[2], 'c': on[3]}, '4', full_diameter=(trial == 0))
        check_duality(Pi, A, ell, {0: on[0], 1: on[1], 'a': on[2], 'c': on[3]})
    print('nearfield plane of order 9 (non-Desarguesian): 4 random frames, all claims checked')

    # 4. the gadget tables printed in the note (q = 5)
    Pi = pg2(5)
    ell = Pi.lines[0]
    A = next(p for p in Pi.points if p not in Pi.pts_on[ell])
    on = sorted(Pi.pts_on[ell], key=str)
    incA, dA = hats(Pi, A, ell, {0: on[0], 1: on[1], 'a': on[2]}, 'AL')
    print_gadget(Pi, incA, dA, 'Gadget of AL (x = incidence, o = removed plane incidence):')
    inc4, d4 = hats(Pi, A, ell, {0: on[0], 1: on[1], 'a': on[2], 'c': on[3]}, '4')
    print_gadget(Pi, inc4, d4, 'Gadget of the four hats:')

    print('ALL CHECKS PASSED' if not FAIL else f'{len(FAIL)} FAILURES')
    return not FAIL


if __name__ == '__main__':
    sys.exit(0 if main() else 1)
