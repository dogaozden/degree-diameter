"""Self-polar hat structures and their polarity graphs (diameter 2).

Frame relative to the conic C: x z = y^2 (q odd): A = (0,1,0) is an external point, ell = A^perp is
the secant y = 0, meeting C in (1,0,0) and (0,0,1).  The conjugation X -> X' on ell
((1,0,z) -> (1,0,-z)) fixes exactly these two points.

  three hats: X_a = (1,0,0),  X_0 = (1,0,u), X_1 = (1,0,-u)              (tau = (0 1))
  four hats:  X_a = (1,0,0), X_c = (0,0,1), X_0 = (1,0,u), X_1 = (1,0,-u) (tau = (0 1))

theta: p -> p^perp, H_s -> K_tau(s), Q -> M (and back) is checked to be a polarity of the
structure: p I L  <=>  theta(L) I theta(p).  The polarity graph on the points (p ~ p' iff
p I theta(p'), p != p') then has diameter 2 because any two points of the structure are
collinear: if p, p' lie on a line L, both are adjacent to theta(L) (or adjacent to each other).
"""
import itertools
import sys
from pg2 import PG2, hats, split, diameter3


def build(q, kind, u):
    Pi = PG2(q)
    F = Pi.F
    A = Pi.pt((0, 1, 0))
    ell = Pi.perp(A)
    X = {'a': Pi.pt((1, 0, 0)), 0: Pi.pt((1, 0, u)), 1: Pi.pt((1, 0, F.neg(u)))}
    if kind == '4':
        X['c'] = Pi.pt((0, 0, 1))
    C = Pi.conic()
    assert ell == Pi.ln((0, 1, 0)) and X['a'] in C and A not in Pi.pts_on[ell]
    inc = hats(Pi, A, ell, X, kind)
    tau = {0: 1, 1: 0, 'a': 'a', 'c': 'c'}

    def theta(x):
        if x[0] in ('p', 'L'):
            return Pi.perp(x)
        return {'H': lambda: ('K', tau[x[1]]), 'K': lambda: ('H', tau[x[1]]),
                'Q': lambda: ('M',), 'M': lambda: ('Q',)}[x[0]]()
    return Pi, inc, theta, C


def polarity_graph(inc, theta):
    pts, lns, lines_on, pts_on = split(inc)
    adj = {p: set() for p in pts}
    absolute = set()
    for p in pts:
        for L in lines_on[p]:
            r = theta(L)
            if r == p:
                absolute.add(p)
            else:
                adj[p].add(r)
    return pts, adj, absolute


def diameter(adj):
    names = list(adj)
    idx = {v: i for i, v in enumerate(names)}
    nb = [0] * len(names)
    for v, s in adj.items():
        for w in s:
            nb[idx[v]] |= 1 << idx[w]
    full = (1 << len(names)) - 1
    best = 0
    for i in range(len(names)):
        ball = fr = 1 << i
        r = 0
        while ball != full:
            nxt, b = 0, fr
            while b:
                low = b & -b
                nxt |= nb[low.bit_length() - 1]
                b ^= low
            fr = nxt & ~ball
            if not fr:
                return None
            ball |= nxt
            r += 1
        best = max(best, r)
    return best


def main(qs):
    for q in qs:
        for kind in ('AL', '4'):
            for u in range(1, q):
                Pi, inc, theta, C = build(q, kind, u)
                F = Pi.F
                if u in (0, F.neg(u)) or len({0, u, F.neg(u)}) < 3:
                    continue
                pts, lns, lines_on, pts_on = split(inc)
                ok_pol = all(((theta(L), theta(p)) in inc) for p, L in inc) and \
                    all(theta(theta(x)) == x for x in pts + lns)
                d3 = diameter3(inc)
                maxdeg = max(max(len(s) for s in lines_on.values()), max(len(s) for s in pts_on.values()))
                ptsG, adj, absolute = polarity_graph(inc, theta)
                assert all(p in adj[r] for p in adj for r in adj[p])
                degs = sorted(len(s) for s in adj.values())
                dG = diameter(adj)
                print(f"q={q} {kind:2s} u={u}: polarity={ok_pol} bip-diam3={d3} maxdeg={maxdeg} |P|={len(pts)} "
                      f"| polarity graph: n={len(ptsG)} maxdeg={degs[-1]} mindeg={degs[0]} "
                      f"#abs={len(absolute)} diam={dG}")
                break


if __name__ == '__main__':
    main([int(a) for a in sys.argv[1:]] or [5, 7, 9, 11, 13])
