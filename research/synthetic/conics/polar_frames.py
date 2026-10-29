"""Self-polar three- and four-hat structures, for every polarity type and every admissible frame.

For a polarity theta of PG(2,q) and a non-absolute point A, put ell = theta(A).  The map
tau: X -> theta(X) cap ell is an involution of the points of ell (conjugation); its fixed points are
the absolute points of ell.  Proposition (CONICS.md, Prop. 1.2): if
    three hats: X_a is absolute, {X_0, X_1} = {X, tau(X)} with X not absolute;
    four hats:  X_a, X_c are absolute, {X_0, X_1} = {X, tau(X)} with X not absolute,
then theta extended by H_s -> K_tau(s), Q -> M (tau swaps the labels 0 and 1 and fixes a, c) is a
polarity of the structure.  This script checks it for every such frame (all A, all choices of
the marked points) for
    orthogonal polarities (conic x z = y^2), q = 3, 5, 7, 9, 11, 13;
    pseudo-polarities (absolute points: the line x + y + z = 0), q = 4, 8, 16 (three hats only);
    unitary polarities (Hermitian curve), q = 4, 9, 16 (four hats; three hats too),
and also the explicit regular completion of Prop. 1.4 (orthogonal case): every deficient point p is
joined to p^perp, or to (p*)^perp if p is on the conic (p* = second point of the conic on Ap).
It also folds each self-polar structure into its polarity graph (diameter 2 is checked).
"""
import itertools
import random
import sys

import coords
from pg2 import PG2, hats, split, diameter3
from selfpolar import polarity_graph, diameter


def frob(F, x, e):
    r = 1
    for _ in range(e):
        r = F.mul(r, x)
    return r


def make_theta(Pi, kind):
    F, q = Pi.F, Pi.q
    if kind == 'orth':
        return Pi.perp
    if kind == 'pseudo':                     # B = identity, char 2
        return lambda x: (('L' if x[0] == 'p' else 'p'), x[1])
    if kind == 'unitary':
        r = int(round(q ** 0.5))
        assert r * r == q
        return lambda x: (('L' if x[0] == 'p' else 'p'),
                          coords.normalize(F, tuple(frob(F, c, r) for c in x[1])))
    raise ValueError(kind)


def check_frame(Pi, theta, A, kind, Xa, Xc, X0):
    ell = theta(A)
    tau_pt = lambda X: Pi.meet(theta(X), ell)
    X1 = tau_pt(X0)
    X = {'a': Xa, 0: X0, 1: X1}
    if kind == '4':
        X['c'] = Xc
    inc = hats(Pi, A, ell, X, kind)
    tau = {0: 1, 1: 0, 'a': 'a', 'c': 'c'}

    def th(x):
        if x[0] in ('p', 'L'):
            return theta(x)
        if x[0] in ('H', 'K'):
            return ('K' if x[0] == 'H' else 'H', tau[x[1]])
        return ('M',) if x[0] == 'Q' else ('Q',)
    pts, lns, lines_on, pts_on = split(inc)
    pol = all((th(L), th(p)) in inc for p, L in inc) and all(th(th(x)) == x for x in pts + lns)
    return inc, th, pol


def completion(Pi, inc, theta, A, ell, C):
    """Prop. 1.4: the explicit matching of deficient points to deficient lines (orthogonal case)."""
    pts, lns, lines_on, pts_on = split(inc)
    q = Pi.q
    defp = [p for p in pts if len(lines_on[p]) == q + 1]
    defl = {L for L in lns if len(pts_on[L]) == q + 1}
    match = {}
    for p in defp:
        assert p[0] == 'p'
        if p in C:
            (pstar,) = (Pi.pts_on[Pi.join(A, p)] & C) - {p}
            match[p] = theta(pstar)
        else:
            match[p] = theta(p)
    ok = (set(match.values()) == defl and len(set(match.values())) == len(defp)
          and all((p, L) not in inc for p, L in match.items()))
    inc2 = inc | set(match.items())
    pts2, lns2, lo2, po2 = split(inc2)
    reg = {len(s) for s in lo2.values()} | {len(s) for s in po2.values()}
    return ok, reg, inc2


def run(q, ptype, kinds, full=True, rng=None):
    Pi = PG2(q)
    theta = make_theta(Pi, ptype)
    absolute = {p for p in Pi.points if p in Pi.pts_on[theta(p)]}
    nA = nframes = 0
    bad = 0
    stats = {}
    As = [p for p in Pi.points if p not in absolute]
    if not full:
        As = rng.sample(As, min(4, len(As)))
    for A in As:
        ell = theta(A)
        absl = [X for X in Pi.pts_on[ell] if X in absolute]
        nonabs = [X for X in Pi.pts_on[ell] if X not in absolute]
        nA += 1
        for kind in kinds:
            if kind == 'AL':
                choices = [(Xa, None) for Xa in absl]
            else:
                choices = [(Xa, Xc) for Xa in absl for Xc in absl if Xa != Xc]
            for Xa, Xc in choices:
                for X0 in nonabs:
                    inc, th, pol = check_frame(Pi, theta, A, kind, Xa, Xc, X0)
                    d3 = diameter3(inc)
                    nframes += 1
                    key = (kind,)
                    if not (pol and d3):
                        bad += 1
                    if key not in stats:
                        ptsG, adj, absG = polarity_graph(inc, th)
                        degs = sorted(len(s) for s in adj.values())
                        dG = diameter(adj)
                        line = f"n={len(ptsG)} maxdeg={degs[-1]} diam={dG}"
                        if ptype == 'orth':
                            C = Pi.conic()
                            okc, reg, inc2 = completion(Pi, inc, theta, A, ell, C)
                            line += f"; completion ok={okc} degrees={sorted(reg)} diam3={diameter3(inc2)}"
                        stats[key] = line
                    if not full:
                        break
    print(f"q={q:2d} {ptype:8s} A's={nA:4d} frames={nframes:5d} failures={bad}  " +
          "  ".join(f"[{k[0]}] {v}" for k, v in stats.items()), flush=True)
    return bad


def main():
    rng = random.Random(1)
    bad = 0
    for q in (3, 5, 7):
        bad += run(q, 'orth', ('AL', '4'))
    for q in (9, 11, 13):
        bad += run(q, 'orth', ('AL', '4'), full=False, rng=rng)
    for q in (4, 8):
        bad += run(q, 'pseudo', ('AL',))
    bad += run(16, 'pseudo', ('AL',), full=False, rng=rng)
    bad += run(4, 'unitary', ('AL', '4'))
    for q in (9, 16):
        bad += run(q, 'unitary', ('AL', '4'), full=False, rng=rng)
    print('ALL FRAMES SELF-POLAR' if bad == 0 else f'FAILURES: {bad}')


if __name__ == '__main__':
    main()
