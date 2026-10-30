r"""
The split Cayley hexagon H(q) in Sage, and the Hermitian spread of H(q).  Shared by d6_*.sage, d7_*.sage, d8_*.sage.
Use:   load('hexagon.sage')      (from the directory research/sage/; set NO_AUTO_CHECK = True first to skip the self-test)

Coordinates (SYNTHETIC.md section 3, research/theorems/POLISHED.md section 6.1; same equations as
research/synthetic/checks/check_d6.py):
    Q(6,q):   x0 x4 + x1 x5 + x2 x6 - x3^2 = 0,   polar form  B(x,y) = x0 y4 + x4 y0 + x1 y5 + x5 y1 + x2 y6 + x6 y2 - 2 x3 y3
    points of H(q)  = the points of the quadric Q(6,q)           (q^6-1)/(q-1) of them  = N = (q+1)(q^4+q^2+1)
    lines of H(q)   = the lines of the quadric whose Pluecker coordinates p_ij = x_i y_j - x_j y_i satisfy the six Tits equations
        p12 = p34,  p54 = p32,  p20 = p35,  p65 = p30,  p01 = p36,  p46 = p31          (N lines)
Vertex labels (first entry 0 = point side, 1 = line side):
    (0, x0, x1, x2, x3, x4, x5, x6)    the point with coordinates x_i in GF(q), first nonzero coordinate normalised to 1
    (1, r_00, ..., r_06, r_10, ..., r_16)   the line, as the reduced row-echelon form of a 2 x 7 matrix whose rows span it
For char 2 the same equations are used (then -x3^2 = x3^2 and B has no x3 term).

hexagon(q, F=None) returns a Hexagon object H with
    H.q, H.F                the order and the field,  H.N = (q+1)(q^4+q^2+1)
    H.points, H.lines       lists of labels
    H.pts_on[L]             tuple of the q+1 point labels on the line L
    H.lines_on[p]           tuple of the q+1 line labels through the point p
    H.graph()               the incidence graph (a Sage Graph on N + N vertices)
    H.dual_graph()          the same graph, with the sides exchanged in the labels (labels (1,..) points, (0,..) lines),
                            i.e. the incidence graph of the dual hexagon
How it is built: for a point x, the Tits conditions and B(x,y)=0 are linear in y; their solution space is a plane of PG(6,q)
(the lines through x form a pencil in it), so the q+1 lines through x are read off from a kernel computation.
Practical sizes: q = 2, 3, 4 take seconds; q = 5 about a minute; q = 7, 8, 9 (N = 19608, 37449, 66430... points) take
hours in pure Sage and are not intended; the D=7 and D=8 files only build such hexagons for q <= 3 or 4.
"""
import itertools


def normalize7(F, v):
    """Scale a nonzero vector so that its first nonzero coordinate is 1."""
    for x in v:
        if x != 0:
            inv = ~x
            return tuple(inv * y for y in v)
    raise ValueError('zero vector')


class Hexagon:
    def __init__(self, q, F, points, lines, pts_on, lines_on):
        self.q, self.F, self.N = q, F, (q + 1) * (q ** 4 + q ** 2 + 1)
        self.points, self.lines, self.pts_on, self.lines_on = points, lines, pts_on, lines_on

    def graph(self):
        G = Graph(multiedges=False, loops=False)
        G.add_vertices(self.points + self.lines)
        G.add_edges((p, L) for L in self.lines for p in self.pts_on[L])
        return G

    def dual_graph(self):
        sw = lambda x: (1 - x[0],) + x[1:]
        G = Graph(multiedges=False, loops=False)
        G.add_vertices([sw(x) for x in self.points + self.lines])
        G.add_edges((sw(p), sw(L)) for L in self.lines for p in self.pts_on[L])
        return G


def quadric_forms(F):
    """Q(x) and B(x,y) of Q(6,q) as functions on 7-tuples over F."""
    Q = lambda x: x[0] * x[4] + x[1] * x[5] + x[2] * x[6] - x[3] ** 2
    B = lambda x, y: (x[0] * y[4] + x[4] * y[0] + x[1] * y[5] + x[5] * y[1] + x[2] * y[6] + x[6] * y[2]
                      - 2 * x[3] * y[3])
    return Q, B


def tits_rows(x):
    """The six Tits equations p_ij(x,y) = ... as linear forms in y for a fixed x: returns six rows (length 7) such that
    row . y = 0  <=>  the equation holds.  p(i,j) = x_i y_j - x_j y_i."""
    def p(i, j):                       # coefficient vector (in y) of p_ij
        r = [0] * 7
        r[j] += x[i]
        r[i] -= x[j]
        return r
    sub = lambda a, b: [s - t for s, t in zip(a, b)]
    return [sub(p(1, 2), p(3, 4)), sub(p(5, 4), p(3, 2)), sub(p(2, 0), p(3, 5)),
            sub(p(6, 5), p(3, 0)), sub(p(0, 1), p(3, 6)), sub(p(4, 6), p(3, 1))]


def hexagon(q, F=None):
    F = F if F is not None else GF(q, 't')
    Q, B = quadric_forms(F)
    pts = set()
    for v in itertools.product(F, repeat=7):
        if any(x != 0 for x in v):
            nv = normalize7(F, v)
            if nv == v and Q(v) == 0:
                pts.add(v)
    pts = sorted(pts, key=lambda t: [str(a) for a in t])
    assert len(pts) == (q ** 6 - 1) // (q - 1)
    lines = {}                                                  # canonical line -> tuple of its points
    for x in pts:
        # y with B(x,y) = 0 and the six Tits equations: a 3-dim space V_x containing x
        M = matrix(F, [[F(c) for c in (x[4], x[5], x[6], -2 * x[3], x[0], x[1], x[2])]] + [[F(c) for c in r] for r in tits_rows(x)])
        K = M.right_kernel()
        assert K.dimension() == 3, (q, x, K.dimension())
        basis = K.basis()
        # the lines through x: spans of x and one more point of the plane V_x (q+1 of them)
        others = [b for b in basis]
        # complete x to a basis of V_x
        Vx = K
        comp = []
        for b in others:
            if matrix(F, [x, b] + comp).rank() == len(comp) + 2:
                comp.append(b)
            if len(comp) == 2:
                break
        u, w = comp
        for (a, b) in [(1, t) for t in F] + [(0, 1)]:
            y = a * u + b * w
            R = matrix(F, [x, y]).echelon_form()
            key = tuple(R[0]) + tuple(R[1])
            if key not in lines:
                members = set()
                for (s, t) in [(1, e) for e in F] + [(0, 1)]:
                    members.add(normalize7(F, tuple(s * R[0][i] + t * R[1][i] for i in range(7))))
                lines[key] = tuple(sorted(members, key=lambda t: [str(a) for a in t]))
    lab = {k: (1,) + k for k in lines}
    points = [(0,) + p for p in pts]
    pts_on = {lab[k]: tuple((0,) + p for p in lines[k]) for k in lines}
    lines_on = {p: [] for p in points}
    for L, ps in pts_on.items():
        for p in ps:
            lines_on[p].append(L)
    lines_on = {p: tuple(v) for p, v in lines_on.items()}
    L = sorted(pts_on, key=lambda t: [str(a) for a in t])
    assert len(L) == len(points) == (q + 1) * (q ** 4 + q ** 2 + 1)
    assert all(len(v) == q + 1 for v in lines_on.values()) and all(len(v) == q + 1 for v in pts_on.values())
    return Hexagon(q, F, points, L, pts_on, lines_on)


# --------------------------------------------------------------------------------------------
# the Hermitian spread
# --------------------------------------------------------------------------------------------

def trace_to_prime(F, z):
    """Absolute trace F -> GF(p) as an element of F."""
    return sum(z ** (F.characteristic() ** i) for i in range(F.degree()))


def hermitian_parameter(F):
    """The constant c of the hyperplane Pi:  q odd: x0 + c x4 = 0 with -c a non-square (the first such c in the list of F);
    q even: x3 = x0 + c x4 with absolute trace Tr(c) = 1 (the first such c)."""
    els = list(F)
    if F.characteristic() == 2:
        return next(d for d in els if d != 0 and trace_to_prime(F, d) == 1)
    sq = {x * x for x in els if x != 0}
    return next(c for c in els if c != 0 and -c not in sq)


def in_Pi(F, c, p, al=0, be=0):
    """Membership of the point p (a label (0, x0..x6)) in the hyperplane Pi_{al,be}; Pi = Pi_{0,0}:
    q odd:  x0 + c x4 + al x2 + be x5 = 0 ;  q even:  x3 = x0 + c x4 + al x2 + be x5 (SYNTHETIC.md 3.2, POLISHED.md Thm 6.5, 6.14)."""
    x = p[1:]
    if F.characteristic() == 2:
        return x[3] == x[0] + c * x[4] + al * x[2] + be * x[5]
    return x[0] + c * x[4] + al * x[2] + be * x[5] == 0


def hermitian_spread(H):
    """The Hermitian spread: the lines of H(q) all of whose points lie in the hyperplane Pi (q^3+1 lines, pairwise opposite,
    covering the points of Pi).  Returns (c, Spts, spread) with Spts the set of point labels in Pi."""
    c = hermitian_parameter(H.F)
    Spts = {p for p in H.points if in_Pi(H.F, c, p)}
    spread = [L for L in H.lines if all(p in Spts for p in H.pts_on[L])]
    assert len(spread) == H.q ** 3 + 1
    return c, Spts, spread


def line_v(H):
    """The distinguished line v of the spread: the line through e1 = (0:1:0:0:0:0:0) and e6 = (0:0:0:0:0:0:1)."""
    F = H.F
    e1 = (0, F(0), F(1), F(0), F(0), F(0), F(0), F(0))
    e6 = (0, F(0), F(0), F(0), F(0), F(0), F(0), F(1))
    (v,) = set(H.lines_on[e1]) & set(H.lines_on[e6])
    return v


def selftest(q):
    H = hexagon(q)
    G = H.graph()
    ok = (G.order() == 2 * H.N and G.is_bipartite() and set(G.degree()) == {q + 1} and G.diameter() == 6 and G.girth() == 12)
    c, Spts, spread = hermitian_spread(H)
    print(f'H({q}): {G.order()} vertices (2N = {2 * H.N}), degrees {sorted(set(G.degree()))}, bipartite {G.is_bipartite()}, '
          f'diameter {G.diameter()}, girth {G.girth()}; Hermitian spread: {len(spread)} lines (q^3+1 = {q ** 3 + 1}) -> '
          f'{"OK" if ok else "MISMATCH"}')
    return ok


if 'NO_AUTO_CHECK' not in globals():
    for q_ in (2, 3):
        assert selftest(q_)
