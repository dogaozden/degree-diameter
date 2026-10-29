#!/usr/bin/env python3
"""Card c8 (squad conics-r1): is the hat structure S self-polar under non-conic polarities?

(a) pseudo-polarity of PG(2,q), q = 4, 8 (char 2): theta(x) = [x], theta([a]) = (a).  Absolute points: x+y+z = 0.
    Three hats: X_a = the absolute point of ell = theta(A), X_0 any other point of ell, X_1 = conjugate of X_0.
    Every non-absolute A is tried.
(b) unitary polarity, r = sqrt(q), q = 4, 9: theta(x) = [x^r], theta([a]) = (a^r).  Absolute: sum x^(r+1) = 0.
    Four hats: X_a, X_c two absolute points of ell, X_0 non-absolute on ell, X_1 its conjugate.
    Three hats: X_a absolute on ell, X_0 non-absolute, X_1 its conjugate.  Every non-absolute A is tried.

S is built from rules R1-R6 of research/squads/conics-r1/BRIEF.md (own code).  theta is extended by
H_s -> K_tau(s), K_s -> H_tau(s), Q <-> M, with tau = (0 1), fixing a (and c).

Per instance the checks are: theta is an involution of the elements of S and swaps points and lines; it preserves
flags (p, L) <-> (theta(L), theta(p)); max degree q+2; incidence graph diameter 3; folded graph G (points of S,
p ~ p' iff p != p' and p lies on theta(p')) is symmetric, has max degree q+2, diameter 2, and q^2+q+5 (three hats)
or q^2+q+6 (four hats) vertices.  Frame sanity: theta(X_s) = lam_tau(s) for every marked point.

Only the GF(q) class is taken from research/plus2/coords/coords.py.  Nothing from research/synthetic is used.
Usage: python check_polarity.py [--parts pseudo4,pseudo8,unitary4,unitary9] [--verbose]
"""
import argparse
import itertools
import sys
import time

import numpy as np

sys.path.insert(0, '/home/user/degree-diameter/research/plus2/coords')
import coords  # noqa: E402  (only coords.GF is used)

PARTS = {
    'pseudo4': ('pseudo', 4), 'pseudo8': ('pseudo', 8),
    'unitary4': ('unitary', 4), 'unitary9': ('unitary', 9),
}
CHECKS = ['invol', 'flag', 'deg', 'inc_diam', 'G_sym', 'G_deg', 'G_diam', 'G_n', 'frame']


class Plane:
    """PG(2,q) with points and lines as normalised triples over coords.GF(q)."""

    def __init__(self, q):
        self.q = q
        self.F = coords.GF(q)
        self.pts = sorted({self.norm(v) for v in itertools.product(range(q), repeat=3) if any(v)})
        self.lns = self.pts
        assert len(self.pts) == q * q + q + 1
        self.thru = {p: [L for L in self.lns if self.dot(p, L) == 0] for p in self.pts}   # lines through p
        self.on = {L: [p for p in self.pts if self.dot(p, L) == 0] for L in self.lns}     # points on L
        self.pg_set = frozenset((('P', p), ('L', L)) for p in self.pts for L in self.thru[p])
        assert len(self.pg_set) == (q * q + q + 1) * (q + 1)

    def norm(self, v):
        i = next(i for i in range(3) if v[i])
        s = self.F.inv(v[i])
        return tuple(self.F.mul(s, t) for t in v)

    def dot(self, u, v):
        F = self.F
        return F.add(F.add(F.mul(u[0], v[0]), F.mul(u[1], v[1])), F.mul(u[2], v[2]))

    def cross(self, u, v):
        """Intersection point of two lines, or line through two points (coordinates as triples)."""
        F = self.F
        return self.norm((F.sub(F.mul(u[1], v[2]), F.mul(u[2], v[1])),
                          F.sub(F.mul(u[2], v[0]), F.mul(u[0], v[2])),
                          F.sub(F.mul(u[0], v[1]), F.mul(u[1], v[0]))))

    def power(self, x, e):
        out = 1
        for _ in range(e):
            out = self.F.mul(out, x)
        return out


def polarity(plane, kind, r):
    """tp: point -> line, tl: line -> point, both dicts; theta(x) = [x] (pseudo) or [x^r] (unitary)."""
    if kind == 'pseudo':
        tp = {p: p for p in plane.pts}
        tl = {L: L for L in plane.lns}
    else:
        tp = {p: plane.norm(tuple(plane.power(x, r) for x in p)) for p in plane.pts}
        tl = {L: plane.norm(tuple(plane.power(x, r) for x in L)) for L in plane.lns}
    # the polarity of PG(2,q) itself
    assert all(tl[tp[p]] == p for p in plane.pts)
    assert all(tp[tl[L]] == L for L in plane.lns)
    assert all((plane.dot(p, L) == 0) == (plane.dot(tl[L], tp[p]) == 0)
               for p in plane.pts for L in plane.lns)
    return tp, tl


def hat_labels(four):
    if four:   # T = {0,c,1}, rho = pi = sigma: 0->c, c->1, 1->0;  tau = (0 1) fixing a, c
        return dict(S=(0, 1, 'a', 'c'), T=(0, 'c', 1), rho={0: 'c', 'c': 1, 1: 0}, pi={0: 'c', 'c': 1, 1: 0},
                    tau={0: 1, 1: 0, 'a': 'a', 'c': 'c'})
    # T = {0,1}, rho = id, pi = (0 1);  tau = (0 1) fixing a
    return dict(S=(0, 1, 'a'), T=(0, 1), rho={0: 0, 1: 1}, pi={0: 1, 1: 0}, tau={0: 1, 1: 0, 'a': 'a'})


def build(plane, tp, tl, A, X, four):
    """Incidence structure S from rules R1-R6, and the extension of theta. X: label -> marked point on ell."""
    lab = hat_labels(four)
    S, T, rho, pi, tau = lab['S'], lab['T'], lab['rho'], lab['pi'], lab['tau']
    ell = tp[A]
    lam = {s: plane.cross(A, X[s]) for s in S}                       # lam_s = A X_s
    # R1: PG incidences minus (X_s, lam_s), s in S, plus (X_t, lam_rho(t)), t in T
    inc = set(plane.pg_set)
    inc -= {(('P', X[s]), ('L', lam[s])) for s in S}
    inc |= {(('P', X[t]), ('L', lam[rho[t]])) for t in T}
    T_pts = {X[t] for t in T}
    T_lam = {lam[t] for t in T}
    ell_star = [p for p in plane.on[ell] if p not in T_pts]           # ell* (R4)
    Lam_star = [L for L in plane.thru[A] if L not in T_lam]           # Lam* (R5)
    for s in S:
        for L in plane.thru[X[s]]:                                    # R2: H_s on lines through X_s, not ell
            if L != ell:
                inc.add((('H', s), ('L', L)))
        for p in plane.on[lam[s]]:                                    # R3: K_s on points of lam_s, not A
            if p != A:
                inc.add((('P', p), ('K', s)))
        inc.add((('H', s), ('M',)))                                   # R4: M contains every H_s
        inc.add((('Q',), ('K', s)))                                   # R5: Q on every K_s
    for p in ell_star:                                                # R4
        inc.add((('P', p), ('M',)))
    for L in Lam_star:                                                # R5
        inc.add((('Q',), ('L', L)))
    inc.add((('P', A), ('K', 'a')))                                   # R6: A on K_a
    inc.add((('H', 'a'), ('L', ell)))                                 # R6: H_a on ell
    for t in T:                                                       # R6: H_t on K_pi(t)
        inc.add((('H', t), ('K', pi[t])))

    Pts = [('P', p) for p in plane.pts] + [('Q',)] + [('H', s) for s in S]
    Lns = [('L', L) for L in plane.lns] + [('M',)] + [('K', s) for s in S]
    pidx = {e: i for i, e in enumerate(Pts)}
    lidx = {e: i for i, e in enumerate(Lns)}
    N = np.zeros((len(Pts), len(Lns)), dtype=bool)
    for e1, e2 in inc:
        N[pidx[e1], lidx[e2]] = True

    th = {('P', p): ('L', tp[p]) for p in plane.pts}
    th.update({('L', L): ('P', tl[L]) for L in plane.lns})
    th[('Q',)] = ('M',)
    th[('M',)] = ('Q',)
    for s in S:
        th[('H', s)] = ('K', tau[s])
        th[('K', s)] = ('H', tau[s])
    theta_pl = np.array([lidx[th[e]] for e in Pts])   # points of S -> lines of S
    theta_lp = np.array([pidx[th[e]] for e in Lns])   # lines of S -> points of S
    return dict(N=N, theta_pl=theta_pl, theta_lp=theta_lp, S=S, four=four, lam=lam, ell=ell)


def diameter(adj):
    """Smallest k such that every pair is joined by a walk of length <= k in the reflexive closure; None if disconnected."""
    n = adj.shape[0]
    R = (adj | np.eye(n, dtype=bool)).astype(np.float32)
    B = R.copy()
    for k in range(1, n + 1):
        if (B > 0).all():
            return k
        B = ((B @ R) > 0).astype(np.float32)
    return None


def run_checks(q, st, plane, tp, X):
    N, theta_pl, theta_lp = st['N'], st['theta_pl'], st['theta_lp']
    nP, nL = N.shape
    res = {}
    ar_p, ar_l = np.arange(nP), np.arange(nL)
    res['invol'] = bool(np.array_equal(theta_lp[theta_pl], ar_p) and np.array_equal(theta_pl[theta_lp], ar_l))
    res['flag'] = bool(np.array_equal(N.T, N[np.ix_(theta_lp, theta_pl)]))
    res['deg'] = bool(max(N.sum(1).max(), N.sum(0).max()) == q + 2)
    adj = np.zeros((nP + nL, nP + nL), dtype=bool)
    adj[:nP, nP:] = N
    adj[nP:, :nP] = N.T
    res['inc_diam'] = bool(diameter(adj) == 3)
    G = N[:, theta_pl].copy()                       # G[p, p'] = p on theta(p')
    np.fill_diagonal(G, False)
    res['G_sym'] = bool(np.array_equal(G, G.T))
    res['G_deg'] = bool(G.sum(1).max() == q + 2)
    res['G_diam'] = bool(diameter(G) == 2)
    res['G_n'] = bool(nP == q * q + q + (6 if st['four'] else 5))
    # frame: theta(X_s) = lam_tau(s) for every marked point
    lam, tau = st['lam'], hat_labels(st['four'])['tau']
    res['frame'] = bool(all(tp[X[s]] == lam[tau[s]] for s in st['S_list']))
    return res


def conj(plane, tp, ell, X):
    """Conjugation on ell: X -> theta(X) cap ell."""
    return plane.cross(tp[X], ell)


def enumerate_instances(plane, tp, kind):
    """Yield (A, four, X) for every non-absolute A and every hat choice in the brief."""
    for A in plane.pts:
        if plane.dot(A, tp[A]) == 0:
            continue                                  # A must be non-absolute
        ell = tp[A]
        on_ell = plane.on[ell]
        absl = [X for X in on_ell if plane.dot(X, tp[X]) == 0]
        nonabs = [X for X in on_ell if plane.dot(X, tp[X]) != 0]
        if kind == 'pseudo' and len(absl) != 1:
            # ell = theta(A) is the absolute line (A = (1,1,1)): every point of ell is absolute, the conjugation
            # on ell is the identity, so the brief's premise (it fixes exactly one point) fails.
            yield A, None, None
            continue
        if kind == 'unitary':
            r1 = 1
            while r1 * r1 < plane.q:
                r1 += 1
            assert len(absl) == r1 + 1, (len(absl), r1)
        for X0 in nonabs:
            X1 = conj(plane, tp, ell, X0)
            assert X1 in on_ell and X1 != X0 and conj(plane, tp, ell, X1) == X0
            assert plane.dot(X1, tp[X1]) != 0
            for Xa in absl:
                yield A, False, {'a': Xa, 0: X0, 1: X1}
                if kind == 'unitary':
                    for Xc in absl:
                        if Xc != Xa:
                            yield A, True, {'a': Xa, 'c': Xc, 0: X0, 1: X1}


def run_part(name, verbose):
    kind, q = PARTS[name]
    r = 1
    while r * r < q:
        r += 1
    if kind == 'unitary':
        assert r * r == q
    t0 = time.time()
    plane = Plane(q)
    tp, tl = polarity(plane, kind, r)
    n_abs = sum(1 for p in plane.pts if plane.dot(p, tp[p]) == 0)
    counts = {'instances': 0, 'pass': 0, 'three_pass': 0, 'three': 0, 'four_pass': 0, 'four': 0}
    fail_tally = {c: 0 for c in CHECKS + ['premise']}
    fail_examples = []
    exceptions = []
    for A, four, X in enumerate_instances(plane, tp, kind):
        counts['instances'] += 1
        if X is None:                                  # degenerate A: the frame premise fails
            counts['three'] += 1
            fail_tally['premise'] += 1
            if len(fail_examples) < 3:
                fail_examples.append((f"{name} A={A} ell=theta(A) is the absolute line", ['premise']))
            continue
        counts['four' if four else 'three'] += 1
        desc = f"{name} A={A} " + ' '.join(f"X_{k}={v}" for k, v in X.items())
        try:
            st = build(plane, tp, tl, A, X, four)
            st['S_list'] = hat_labels(four)['S']
            res = run_checks(q, st, plane, tp, X)
        except Exception as exc:  # a bug or a structural failure: count it as a failed instance
            exceptions.append(f"{desc}: {type(exc).__name__}: {exc}")
            continue
        ok = all(res.values())
        for c in CHECKS:
            if not res[c]:
                fail_tally[c] += 1
        if ok:
            counts['pass'] += 1
            counts['four_pass' if four else 'three_pass'] += 1
        elif len(fail_examples) < 3:
            fail_examples.append((desc, [c for c in CHECKS if not res[c]]))
    dt = time.time() - t0
    print(f"== {name}: q={q}, theta(x)={'[x]' if kind == 'pseudo' else f'[x^{r}]'}; absolute points={n_abs}; "
          f"time {dt:.1f}s")
    print(f"   instances {counts['instances']} (three hats {counts['three']}, four hats {counts['four']}); "
          f"pass {counts['pass']} (three {counts['three_pass']}, four {counts['four_pass']})")
    print(f"   failing checks (count over instances): {{{', '.join(f'{c}: {v}' for c, v in fail_tally.items() if v)}}}")
    if exceptions:
        print(f"   exceptions: {len(exceptions)}; first: {exceptions[0]}")
    if verbose:
        for d, cs in fail_examples:
            print(f"   fail: {d} -> {cs}")
    return counts, exceptions


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--parts', default=','.join(PARTS))
    ap.add_argument('--verbose', action='store_true')
    args = ap.parse_args()
    total = {'instances': 0, 'pass': 0}
    exc_total = 0
    for name in args.parts.split(','):
        counts, exc = run_part(name, args.verbose)
        total['instances'] += counts['instances']
        total['pass'] += counts['pass']
        exc_total += len(exc)
    print(f"TOTAL instances {total['instances']}, pass {total['pass']}, exceptions {exc_total}, "
          f"valid {total['pass'] == total['instances'] and exc_total == 0}")


if __name__ == '__main__':
    main()
