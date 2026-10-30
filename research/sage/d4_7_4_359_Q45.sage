r"""
Diameter 4, the (7,4) example on 359 vertices: the quadrangle Q(4,5) with one clone of each of the 26 points
of an ovoid and 21 shadow lines with stand-ins ("Theorem B", SYNTHETIC.md section 2.6; data from
research/synthetic/checks/q4_359_lines.json, found by an integer program).  Maximum degree 7, diameter 4.

Run:   sage d4_7_4_359_Q45.sage

Coordinates.  Q(4,5): the parabolic quadric  Q(x) = x0^2 + x1 x2 + x3 x4 = 0  in PG(4,5) (research/gq4/gq_clones.py,
function q4), a generalized quadrangle of order (5,5): 156 points, 156 lines.
    (0, x0, x1, x2, x3, x4)    a point (first nonzero coordinate 1)
    (1, 'Q', r00, ..., r14)    a line of the quadric: the reduced row echelon form of the 2 x 5 matrix of two of its points
    (0, 'clone', point)        the clone of an ovoid point: on exactly the lines through that point
    (1, 'shadow', mu, L)       the shadow line number mu over the line L: one point over each point of L, namely
                               the point itself or its clone (the "stand-in")
The ovoid O = { x4 = lam * x3 } with -lam a non-square (26 = q^2+1 points meeting every line once).
"""
import itertools

# The 21 shadow lines.  Each entry: (P1, P2, S): the line through the points P1 and P2, and S the list of points of
# the line whose stand-in is their CLONE (all other points of the line stand in for themselves).
SHADOW_LINES = [
    ((0, 0, 0, 0, 1), (0, 1, 0, 0, 0), []),
    ((0, 0, 0, 1, 0), (0, 1, 0, 0, 0), [(0, 1, 0, 0, 0)]),
    ((0, 0, 1, 0, 0), (1, 0, 0, 2, 2), []),
    ((0, 0, 1, 0, 1), (1, 2, 0, 3, 3), []),
    ((0, 0, 1, 0, 2), (1, 1, 0, 2, 2), []),
    ((0, 0, 1, 0, 4), (1, 3, 0, 3, 3), []),
    ((0, 0, 1, 1, 0), (1, 4, 0, 4, 1), []),
    ((0, 0, 1, 2, 0), (1, 4, 0, 3, 3), []),
    ((0, 0, 1, 3, 0), (1, 2, 0, 4, 1), [(1, 2, 3, 3, 1)]),
    ((0, 0, 1, 4, 0), (1, 4, 0, 1, 4), []),
    ((0, 1, 1, 1, 4), (1, 0, 3, 4, 1), []),
    ((0, 1, 1, 2, 2), (1, 0, 0, 1, 4), []),
    ((0, 1, 1, 3, 3), (1, 0, 2, 3, 3), []),
    ((0, 1, 1, 4, 1), (1, 0, 2, 4, 1), [(1, 4, 1, 0, 0)]),
    ((0, 1, 2, 1, 3), (1, 0, 3, 3, 3), []),
    ((0, 1, 2, 2, 4), (1, 0, 3, 1, 4), []),
    ((0, 1, 3, 2, 1), (1, 0, 1, 3, 3), []),
    ((0, 1, 3, 3, 4), (1, 0, 4, 1, 4), []),
    ((0, 1, 4, 1, 1), (1, 0, 4, 3, 3), []),
    ((0, 1, 4, 2, 3), (1, 0, 0, 3, 3), []),
    ((0, 1, 4, 4, 4), (1, 0, 0, 4, 1), [(1, 2, 3, 2, 4)]),
]


def normalize(v):
    for x in v:
        if x != 0:
            inv = ~x
            return tuple(inv * y for y in v)
    raise ValueError


def quadric_Q45(q=5):
    """Q(4,q), q prime: returns (points, lines, onl, ovoid) with points = list of 5-tuples over GF(q),
    lines = list of labels, onl[label] = list of points, ovoid = set of points."""
    F = GF(q)
    Qf = lambda v: v[0] ** 2 + v[1] * v[2] + v[3] * v[4]
    B = lambda u, v: 2 * u[0] * v[0] + u[1] * v[2] + u[2] * v[1] + u[3] * v[4] + u[4] * v[3]     # polar form
    pts = sorted({normalize(v) for v in itertools.product(F, repeat=5) if any(x != 0 for x in v) and Qf(v) == 0},
                 key=lambda t: [int(x) for x in t])
    lines, onl = [], {}
    for i, p in enumerate(pts):
        for r in pts[i + 1:]:
            if B(p, r) == 0:                                    # p, r orthogonal points of the quadric: the line pr is on it
                M = matrix(F, [p, r]).echelon_form()
                L = (1, 'Q') + tuple(M.list())
                if L not in onl:
                    S = {p, r} | {normalize(tuple(p[k] + a * r[k] for k in range(5))) for a in F if a != 0}
                    onl[L] = sorted(S, key=lambda t: [int(x) for x in t])
                    lines.append(L)
    nonsq = {x * x for x in F if x != 0}
    lam = next(l for l in F if l != 0 and -l not in nonsq)
    ovoid = {p for p in pts if p[4] == lam * p[3]}
    return pts, lines, onl, ovoid


def build_d4_7_4_359():
    r"""Q(4,5) + 26 clones + 21 shadow lines: 359 vertices, maximum degree 7, diameter 4."""
    F = GF(5)
    pts, lines, onl, ovoid = quadric_Q45(5)
    G = Graph(multiedges=False, loops=False)
    # Q(4,5) itself: points (0, ...) and lines (1,'Q',...) with their incidences
    lines_on = {p: [] for p in pts}
    for L in lines:
        for p in onl[L]:
            G.add_edge((0,) + p, L)
            lines_on[p].append(L)
    # one clone of each ovoid point, on exactly the lines through its point
    for p in sorted(ovoid, key=lambda t: [int(x) for x in t]):
        for L in lines_on[p]:
            G.add_edge((0, 'clone', (0,) + p), L)
    # the 21 shadow lines: one point over each point of the underlying line L, the point itself, or its clone if it is
    # one of the listed stand-ins (a clone of an ovoid point)
    for mu, (P1, P2, clones) in enumerate(SHADOW_LINES):
        p1, p2 = [tuple(F(x) for x in P) for P in (P1, P2)]
        L = (1, 'Q') + tuple(matrix(F, [p1, p2]).echelon_form().list())
        sh = (1, 'shadow', mu, L)
        use_clone = {tuple(F(x) for x in c) for c in clones}
        for p in onl[L]:
            assert p not in use_clone or p in ovoid
            G.add_edge((0, 'clone', (0,) + p) if p in use_clone else (0,) + p, sh)
    return G


# --------------------------------------------------------------------------------------------
# check
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


def check(q=5):
    assert q == 5
    pts, lines, onl, ovoid = quadric_Q45(5)
    print(f'Q(4,5): {len(pts)} points, {len(lines)} lines, ovoid of {len(ovoid)} points meeting every line once: '
          f'{all(len(set(onl[L]) & ovoid) == 1 for L in lines)}')
    G = build_d4_7_4_359()
    return report(G, 359, 7, 4, name='(7,4): Q(4,5) + 26 clones + 21 shadow lines')


if 'NO_AUTO_CHECK' not in globals():
    assert check(5)
