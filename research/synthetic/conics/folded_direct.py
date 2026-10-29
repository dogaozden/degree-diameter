"""Check the direct description of the folded four hats (CONICS.md, after Corollary 1.6):
the Erdos-Renyi graph of PG(2,q) (p ~ r iff p on r^perp, p != r) with the edge X_0 X_1 replaced by X_0 Z', plus
Q ~ Z, Q ~ the q-3 unmarked points of ell, Q ~ every hat; H_s ~ the q points of lam_{tau(s)} other than A;
H_a ~ A; H_0 ~ H_c.  Compared with the polarity graph computed from the incidence structure."""
from selfpolar import build, polarity_graph

for q in (3, 5, 7, 9, 11, 13):
    Pi, inc, theta, C = build(q, '4', 1)
    pts, adj, absolute = polarity_graph(inc, theta)
    A = Pi.pt((0, 1, 0)); ell = Pi.perp(A)
    F = Pi.F
    X = {'a': Pi.pt((1, 0, 0)), 'c': Pi.pt((0, 0, 1)), 0: Pi.pt((1, 0, 1)), 1: Pi.pt((1, 0, F.neg(1)))}
    tau = {0: 1, 1: 0, 'a': 'a', 'c': 'c'}
    E = set()
    for p in Pi.points:
        for r in Pi.pts_on[Pi.perp(p)]:
            if r != p:
                E.add(frozenset((p, r)))
    E.discard(frozenset((X[0], X[1])))
    E.add(frozenset((X[0], X['c'])))
    marked = set(X.values())
    for p in Pi.pts_on[ell]:
        if p not in marked or p == X['a']:
            E.add(frozenset((('Q',), p)))
    for s in X:
        E.add(frozenset((('Q',), ('H', s))))
        lam = Pi.join(A, X[tau[s]])
        for p in Pi.pts_on[lam] - {A}:
            E.add(frozenset((('H', s), p)))
    E.add(frozenset((('H', 'a'), A)))
    E.add(frozenset((('H', 0), ('H', 'c'))))
    E2 = {frozenset((p, r)) for p in adj for r in adj[p]}
    print(f'q={q}: direct description equals the polarity graph: {E == E2}  (|E|={len(E)})')
