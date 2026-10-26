"""Local dualities on two points (Proposition 6.4 of D5_QUADRANGLE.md): for non-collinear points x, y of a GQ H of
order (s,s) and non-concurrent lines l, m, a bijection M: points -> lines with M(x) = l, M(y) = m,
M({x,y}^perp) = {l,m}^perp, M(Gamma_2(x)) = Gamma_2(l), M(Gamma_2(y)) = Gamma_2(m); the rest arbitrary
(here: sorted order onto sorted order, so M is explicit)."""
import numpy as np


def local_duality_pair(H, x, y, l, m):
    assert not H.col[x, y] and x != y and not H.con[l, m] and l != m
    n = H.np
    M = [-1] * n
    used = set()
    def put(a, b):
        assert M[a] == -1 and b not in used
        M[a] = b; used.add(b)
    put(x, l); put(y, m)
    cxy = [p for p in np.nonzero(H.col[x] & H.col[y])[0]]
    clm = [k for k in np.nonzero(H.con[l] & H.con[m])[0]]
    assert len(cxy) == len(clm)
    for a, b in zip(sorted(cxy), sorted(clm)): put(a, b)
    for (u, w) in ((x, l), (y, m)):
        A = sorted(p for p in np.nonzero(H.col[u])[0] if M[p] == -1)
        B = sorted(k for k in np.nonzero(H.con[w])[0] if k not in used)
        assert len(A) == len(B)
        for a, b in zip(A, B): put(a, b)
    rest_a = [a for a in range(n) if M[a] == -1]
    rest_b = sorted(set(range(H.nl)) - used)
    for a, b in zip(rest_a, rest_b): put(a, b)
    return M


def pick_pair(H, avoid_pts=(), avoid_lines=()):
    """first non-collinear point pair and non-concurrent line pair outside the given sets"""
    pts = [p for p in range(H.np) if p not in set(avoid_pts)]
    x = pts[0]; y = next(p for p in pts[1:] if not H.col[x, p])
    lns = [k for k in range(H.nl) if k not in set(avoid_lines)]
    l = lns[0]; m = next(k for k in lns[1:] if not H.con[l, k])
    return x, y, l, m


if __name__ == '__main__':
    from gqlib import W, Q4
    from repair import exact_conditions, brute_bad
    for G in (W(3), Q4(3), W(5), Q4(5)):
        x, y, l, m = pick_pair(G)
        M = local_duality_pair(G, x, y, l, m)
        ok, f = exact_conditions(G, 'H', 'H', M, {x, y})
        print(G.name, 'pair', (x, y), '->', (l, m), 'exact', ok, 'brute_bad', brute_bad(G, 'H', 'H', M, {x, y}))
