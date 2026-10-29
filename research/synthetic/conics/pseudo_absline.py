"""Pseudo-polarity theta (B = identity, q even) with A = (1,1,1), so that ell = theta(A) = [1,1,1] is the line of
absolute points.  Then tau = identity on ell and Lemma 1.2 applies to the three hats with H_s <-> K_s, for ANY three
marked points.  Checked for every ordered choice of (X_a, X_0, X_1) on ell, q = 4, 8."""
import itertools
from pg2 import PG2, hats, split, diameter3
from polar_frames import make_theta
from selfpolar import polarity_graph, diameter

for q in (4, 8):
    Pi = PG2(q)
    theta = make_theta(Pi, 'pseudo')
    A = Pi.pt((1, 1, 1))
    ell = theta(A)
    assert A not in Pi.pts_on[ell] and all(p in Pi.pts_on[theta(p)] for p in Pi.pts_on[ell])
    n = ok = 0
    for Xa, X0, X1 in itertools.permutations(sorted(Pi.pts_on[ell]), 3):
        inc = hats(Pi, A, ell, {'a': Xa, 0: X0, 1: X1}, 'AL')

        def th(x):
            if x[0] in ('p', 'L'):
                return theta(x)
            if x[0] in ('H', 'K'):
                return ('K' if x[0] == 'H' else 'H', x[1])
            return ('M',) if x[0] == 'Q' else ('Q',)
        pts, lns, lo, po = split(inc)
        pol = all((th(L), th(p)) in inc for p, L in inc) and all(th(th(x)) == x for x in pts + lns)
        good = pol and diameter3(inc)
        if good and n == 0:
            _, adj, _ = polarity_graph(inc, th)
            print(f'  q={q}: folded n={len(adj)} maxdeg={max(len(s) for s in adj.values())} diam={diameter(adj)}')
        n += 1
        ok += good
    print(f'q={q}: ell = absolute line, tau = id: {ok}/{n} three-hat frames self-polar with H_s <-> K_s')
