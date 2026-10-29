"""The four hats without changing the plane (research/plus3/plus3.tex, Proposition 'zero') in a conic frame.

Labels a, 1, 2, 3 and the 3-cycle s = (1 2 3).  Conic frame: A external, ell = A^perp, X_a = Z, X_2 = Z',
{X_1, X_3} a conjugate pair; tau = (1 3) fixes a and 2 and inverts s.  Rules (plus3.tex, table of Prop. zero):
  Q:   every line through A except AX_1, AX_2, AX_3;            new: K_a, K_1, K_2, K_3
  H_a: every line through X_a except AX_a;                      new: M, K_a
  H_i: every line through X_i except ell and AX_i; and AX_s(i);  new: M, K_i
  M:   every point of ell except X_1, X_2, X_3;                 new: H_a, H_1, H_2, H_3
  K_a: every point of AX_a except X_a;                          new: Q, H_a
  K_i: every point of AX_i except A and X_i; and X_s^-1(i);     new: Q, H_i
Checks: theta (conic polarity, H_x <-> K_tau(x), Q <-> M) is a polarity; diameter 3; max degree q+2; the folded
graph is the Erdos-Renyi graph of PG(2,q) (unchanged) plus 5 vertices, of diameter 2.  Also: the polarity
completion of Prop. 1.10 makes it (q+2)-regular."""
from pg2 import PG2, split, diameter3
from selfpolar import polarity_graph, diameter

for q in (3, 5, 7, 9, 11, 13):
    Pi = PG2(q)
    F = Pi.F
    A = Pi.pt((0, 1, 0)); ell = Pi.perp(A)
    X = {'a': Pi.pt((1, 0, 0)), 2: Pi.pt((0, 0, 1)), 1: Pi.pt((1, 0, 1)), 3: Pi.pt((1, 0, F.neg(1)))}
    s = {1: 2, 2: 3, 3: 1}; si = {v: k for k, v in s.items()}
    tau = {'a': 'a', 2: 2, 1: 3, 3: 1}
    AX = {k: Pi.join(A, x) for k, x in X.items()}
    inc = set(Pi.inc)
    for L in Pi.lines_on[A] - {AX[1], AX[2], AX[3]}:
        inc.add((('Q',), L))
    for k in X:
        inc.add((('Q',), ('K', k)))
    for L in Pi.lines_on[X['a']] - {AX['a']}:
        inc.add((('H', 'a'), L))
    inc |= {(('H', 'a'), ('M',)), (('H', 'a'), ('K', 'a'))}
    for i in (1, 2, 3):
        for L in Pi.lines_on[X[i]] - {ell, AX[i]}:
            inc.add((('H', i), L))
        inc |= {(('H', i), AX[s[i]]), (('H', i), ('M',)), (('H', i), ('K', i))}
    for p in Pi.pts_on[ell] - {X[1], X[2], X[3]}:
        inc.add((p, ('M',)))
    for p in Pi.pts_on[AX['a']] - {X['a']}:
        inc.add((p, ('K', 'a')))
    for i in (1, 2, 3):
        for p in Pi.pts_on[AX[i]] - {A, X[i]}:
            inc.add((p, ('K', i)))
        inc.add((X[si[i]], ('K', i)))

    def th(x):
        if x[0] in ('p', 'L'):
            return Pi.perp(x)
        if x[0] in ('H', 'K'):
            return ('K' if x[0] == 'H' else 'H', tau[x[1]])
        return ('M',) if x[0] == 'Q' else ('Q',)
    pts, lns, lo, po = split(inc)
    pol = all((th(L), th(p)) in inc for p, L in inc) and all(th(th(x)) == x for x in pts + lns)
    md = max(max(len(v) for v in lo.values()), max(len(v) for v in po.values()))
    _, adj, absolute = polarity_graph(inc, th)
    er = all((r in adj[p]) == (p != r and r in Pi.pts_on[Pi.perp(p)]) for p in Pi.points for r in Pi.points)
    print(f'q={q:2d}: polarity={pol} diameter3={diameter3(inc)} maxdeg={md} | folded: n={len(adj)} '
          f'maxdeg={max(len(v) for v in adj.values())} diam={diameter(adj)} old part = ER graph: {er}')
    # the polarity completion of Prop. 1.10: p -> p^perp off the conic, p -> (p*)^perp on it
    C = Pi.conic()
    defp = [p for p in pts if len(lo[p]) == q + 1]
    defl = {L for L in lns if len(po[L]) == q + 1}
    mu = {}
    for p in defp:
        if p in C:
            (ps,) = (Pi.pts_on[Pi.join(A, p)] & C) - {p}
            mu[p] = Pi.perp(ps)
        else:
            mu[p] = Pi.perp(p)
    ok = set(mu.values()) == defl and len(defl) == len(defp) and all((p, L) not in inc for p, L in mu.items())
    inc2 = inc | set(mu.items())
    _, _, lo2, po2 = split(inc2)
    degs = {len(v) for v in lo2.values()} | {len(v) for v in po2.values()}
    print(f'        completion: {len(defp)} deficient points, matching ok={ok}, degrees={sorted(degs)}, '
          f'diameter3={diameter3(inc2)}, self-polar={all((th(L), th(p)) in inc2 for p, L in inc2)}')
