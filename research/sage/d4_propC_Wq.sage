r"""
Diameter 4, Proposition C: a 2-ovoid and a spread of the symplectic quadrangle W(q), q odd prime
(the "Singer" model: PG(3,q) = GF(q^4)^* / GF(q)^*).  Clone every point of the 2-ovoid O once and put two
shadow lines over every line of the spread; complete to a (q+3)-regular graph on 2 (q^2+1)(q+3) vertices,
diameter 4.   Sources: SYNTHETIC.md sections 2.1-2.4 (Corollary 2.3, Proposition C), research/synthetic/checks/check_d4.py
(`cyclic_W3`, `corollary_C1`).

Run:   sage d4_propC_Wq.sage            (checks q = 3 and q = 5)

Model.  E = GF(q^4) = F[x]/(f), g = x a primitive element (f the first monic quartic x^4+c3x^3+c2x^2+c1x+c0,
c0 != 0, in the order of (c0,c1,c2,c3) in {0..q-1}^4, for which x has order q^4-1).  N = (q+1)(q^2+1).
The point number i in Z_N is the point of PG(3,q) with coordinates (c_0:c_1:c_2:c_3) of g^i = sum c_k g^k.
The symplectic form is b(u,v) = Tr( d u v^(q^2) ),  d = g^((q^2+1)/2)   (alternating, since d^(q^2) = -d).
    (0, x0, x1, x2, x3)        the point (x0:x1:x2:x3) of W(q), first nonzero coordinate 1
    (1, 'W', r00, ..., r13)    a totally isotropic line of W(q): the entries of the reduced row echelon form of the
                               2 x 4 matrix of two of its points (this identifies the line of PG(3,q))
    (0, 'clone', point)        the clone of a point of the 2-ovoid: on exactly the lines through the point
    (1, 'shadow', L, k)        the shadow line number k = 0, 1 over the spread line L: it contains the same points as L
                               (every stand-in is the point itself)
O = the points number i with i mod (q+1) in {0, q}  (2(q^2+1) points meeting every line in exactly 2 points).
Spread = the q^2+1 lines { g^(i + (q^2+1) k) : k = 0..q } for i = 0..q^2  (the Desarguesian spread: GF(q^2)-lines).
"""
import itertools


def normalize(v):
    for x in v:
        if x != 0:
            inv = ~x
            return tuple(inv * y for y in v)
    raise ValueError


def cyclic_W(q):
    r"""The model above.  Returns a dictionary with F, E, g, N, pts (labels by number), lines (label -> frozenset of
    point numbers), O (set of point numbers), spread (list of line labels in the order of i = 0..q^2)."""
    assert ZZ(q).is_prime() and q % 2 == 1
    F = GF(q)
    R = PolynomialRing(F, 'x')
    xx = R.gen()
    Q4 = q ** 4
    N = (q + 1) * (q * q + 1)
    for c in itertools.product(range(q), repeat=4):
        if c[0] == 0:
            continue
        f = xx ** 4 + c[3] * xx ** 3 + c[2] * xx ** 2 + c[1] * xx + c[0]
        if not f.is_irreducible():
            continue
        E = GF(Q4, 'g', modulus=f)
        g = E.gen()
        if g.multiplicative_order() == Q4 - 1:
            break
    pw = [g ** i for i in range(Q4 - 1)]
    vec = lambda e: tuple(F(t) for t in e.list())
    pts = [(0,) + normalize(vec(pw[i])) for i in range(N)]
    number = {p: i for i, p in enumerate(pts)}
    d = g ** ((q * q + 1) // 2)
    form = lambda i, k: (d * pw[i] * pw[(k * q * q) % (Q4 - 1)]).trace()      # b(g^i, g^k) = Tr(d g^i g^(k q^2))
    lines = {}
    for i in range(N):
        for k in range(i + 1, N):
            if form(i, k) == 0:
                S = {i, k} | {number[(0,) + normalize(tuple(a * u + w for u, w in zip(pts[i][1:], pts[k][1:])))]
                              for a in F}
                S2 = frozenset(S)
                if S2 not in lines.values():
                    M = matrix(F, [pts[i][1:], pts[k][1:]]).echelon_form()
                    lines[(1, 'W') + tuple(M.list())] = S2
    O = {i for i in range(N) if i % (q + 1) in (0, q)}
    K = q * q + 1
    spread = []
    for i in range(K):
        S = frozenset((i + K * k) % N for k in range(q + 1))
        spread.append(next(L for L, s in lines.items() if s == S))
    return dict(F=F, E=E, g=g, N=N, pts=pts, lines=lines, O=O, spread=spread)


def build_d4_propC(q, W=None, spread_order=None, complete=True):
    r"""
    The Proposition C graph on 2 (q^2+1)(q+3) vertices.
    spread_order  optional order (a list of spread line labels) used only for the completion step
    complete      if False return the core (clones + shadow lines, degrees q+3 / q+1), without the completion
    """
    W = W if W is not None else cyclic_W(q)
    pts, lines, O, spread = W['pts'], W['lines'], W['O'], W['spread']
    G = Graph(multiedges=False, loops=False)
    G.add_vertices(pts + list(lines))
    lines_on = {i: [] for i in range(W['N'])}
    # W(q) itself: the point i is on the isotropic line L iff i is in the point set of L
    for L, S in lines.items():
        for i in S:
            G.add_edge(pts[i], L)
            lines_on[i].append(L)
    # clones: one clone of each point of the 2-ovoid O; it is on exactly the lines through the point
    clones = []
    for i in sorted(O):
        cl = (0, 'clone', pts[i])
        clones.append(cl)
        for L in lines_on[i]:
            G.add_edge(cl, L)
    # shadow lines: two over each spread line L, with the same points as L (all stand-ins original)
    shadows = []
    for L in (spread_order if spread_order is not None else spread):
        for k in (0, 1):
            sh = (1, 'shadow', L, k)
            shadows.append(sh)
            for i in lines[L]:
                G.add_edge(pts[i], sh)
    if complete:
        # completion (SYNTHETIC.md 2.4): the i-th clone is joined to the shadow lines number 2i and 2i+1
        # (indices modulo the number 2(q^2+1) of shadow lines); these pairs are anti-flags because
        # no clone is on a shadow line.
        b = len(shadows)
        for i, cl in enumerate(clones):
            for k in (0, 1):
                assert not G.has_edge(cl, shadows[(2 * i + k) % b])
                G.add_edge(cl, shadows[(2 * i + k) % b])
    return G


# --------------------------------------------------------------------------------------------
# checks
# --------------------------------------------------------------------------------------------

def report(G, expect_n, expect_deg, expect_diam, bip=True, name=''):
    n = G.order()
    maxdeg = max(G.degree())
    isbip = G.is_bipartite()
    diam = G.diameter()
    ok = (n == expect_n and maxdeg == expect_deg and isbip == bip and diam == expect_diam)
    print(f'{name}: vertices {n} (expected {expect_n}), max degree {maxdeg} (expected {expect_deg}), '
          f'bipartite {isbip}, diameter {diam} (expected {expect_diam})  ->  {"OK" if ok else "MISMATCH"}')
    return ok


def check(q):
    W = cyclic_W(q)
    lines, O, spread = W['lines'], W['O'], W['spread']
    ok = True
    N = W['N']
    ok &= (len(lines) == N and all(len(S) == q + 1 for S in lines.values()))
    two = all(len(S & O) == 2 for S in lines.values())
    cover = sorted(i for L in spread for i in lines[L]) == list(range(N))
    print(f'W({q}): {N} points, {len(lines)} lines; O has {len(O)} points and meets every line twice: {two}; '
          f'the {len(spread)} spread lines partition the points: {cover}')
    ok &= two and cover and len(O) == 2 * (q * q + 1)
    core = build_d4_propC(q, W, complete=False)
    print(f'core (before the completion): degrees {sorted(set(core.degree()))}')
    G = build_d4_propC(q, W)
    ok &= report(G, 2 * (q * q + 1) * (q + 3), q + 3, 4, name=f'Proposition C, q={q}')
    print(f'   (q+3)-regular: {set(G.degree()) == {q + 3}}')
    ok &= (set(G.degree()) == {q + 3})
    return ok


if 'NO_AUTO_CHECK' not in globals():
    for q_ in (3, 5):
        assert check(q_)
