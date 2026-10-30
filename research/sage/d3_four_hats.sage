r"""
Diameter 3: the four-hat construction (+2 over Araujo-Pardo--Lopez) in PG(2,q), q >= 4.

Notation: research/plus2/coords/coords-standalone.tex (= coords.tex) and SYNTHETIC.md section 1.
Run:   sage d3_four_hats.sage            (checks q = 4 and q = 5)
or:    sage -c 'load("d3_four_hats.sage"); G = build_d3_four_hats(7); print(G)'

Vertex labels (the geometric objects themselves; first entry 0 = point side, 1 = line side):
    (0, x, y, z)   the point (x:y:z) of PG(2,q), first nonzero coordinate normalised to 1
    (1, u, v, w)   the line  [u:v:w], first nonzero coordinate normalised to 1
                   (x:y:z) lies on [u:v:w]  iff  u*x + v*y + w*z = 0
    (0, 'Q')       the new point Q          (0, 'H', s)  the hat point H_s, s in S
    (1, 'M')       the new line  M          (1, 'K', s)  the hat line  K_s, s in S
The coordinates x, y, z, u, v, w, s are elements of GF(q).

The frame (coords.tex, "Notation"):
    ell = [1:0:0]  (the line x = 0)      A = (1:0:0)       (A is not on ell)
    X_t = (0:t:1), t in GF(q), and P = (0:1:0)             (the q+1 points of ell)
    lam_t = [0:1:-t], t in GF(q), lam_inf = [0:0:1]        (the q+1 lines through A)
    X_t is on lam_t, and P is on lam_inf.
Four hats: S = {0,1,a,c}, T = {0,1,c}, rotation sigma: 0 -> c -> 1 -> 0 on T.
Three hats (Araujo-Pardo--Lopez): S = {0,1,a}, T = {0,1}, no rotation.
"""
import itertools


# --------------------------------------------------------------------------------------------
# PG(2,q) in coordinates
# --------------------------------------------------------------------------------------------

def normalize(v):
    """Scale a nonzero triple so that its first nonzero coordinate is 1."""
    for x in v:
        if x != 0:
            inv = ~x
            return tuple(inv * y for y in v)
    raise ValueError('zero vector')


def pg2_triples(F):
    """The q^2+q+1 normalised triples over F (they name both points and lines)."""
    seen = set()
    for v in itertools.product(F, repeat=3):
        if any(x != 0 for x in v):
            seen.add(normalize(v))
    return sorted(seen, key=lambda t: [str(x) for x in t])


def d3_notation(F):
    """Returns the frame as a dictionary of functions and constants (coords.tex, Notation)."""
    pt = lambda x, y, z: (0,) + normalize((F(x), F(y), F(z)))     # the point (x:y:z)
    ln = lambda u, v, w: (1,) + normalize((F(u), F(v), F(w)))     # the line  [u:v:w]
    return dict(
        pt=pt, ln=ln,
        A=pt(1, 0, 0), P=pt(0, 1, 0),
        ell=ln(1, 0, 0), lam_inf=ln(0, 0, 1),
        X=lambda t: pt(0, t, 1),            # X_t = (0:t:1)
        lam=lambda t: ln(0, 1, -F(t)),      # lam_t = [0:1:-t]
    )


# --------------------------------------------------------------------------------------------
# the construction
# --------------------------------------------------------------------------------------------

def build_d3_four_hats(q, a=None, c=None, filler=False, F=None, three_hats=False):
    r"""
    The incidence graph of the four-hat structure S(q; a, c) of coords.tex, as a Sage Graph.

    q          prime power, q >= 4 (q >= 3 for three_hats)
    a, c       the labels a, c in GF(q) \ {0,1}, distinct (default: the first two admissible ones)
    filler     if True, add the optional step (C7): join every point of degree q+1 to the line
               delta(p), which makes the graph (q+2)-regular
    F          the field GF(q) to use (default GF(q, 't'))
    three_hats if True build the Araujo-Pardo--Lopez structure A (three hats, S = {0,1,a}) instead;
               then c must be None
    """
    F = F if F is not None else GF(q, 't')
    els = list(F)                                     # 0 first, 1 second in Sage's list
    zero, one = F(0), F(1)
    if three_hats:
        assert c is None
        a = F(a) if a is not None else [x for x in els if x not in (zero, one)][0]
        S, T = [zero, one, a], [zero, one]
        sigma = {}
    else:
        assert q >= 4
        rest = [x for x in els if x not in (zero, one)]
        a = F(a) if a is not None else rest[0]
        c = F(c) if c is not None else [x for x in rest if x != a][0]
        assert len({zero, one, a, c}) == 4
        S, T = [zero, one, a, c], [zero, one, c]
        sigma = {zero: c, c: one, one: zero}          # the 3-cycle (0 c 1) on T
    nt = d3_notation(F)
    pt, ln, A, P, ell, lam_inf, X, lam = (nt[k] for k in ('pt', 'ln', 'A', 'P', 'ell', 'lam_inf', 'X', 'lam'))
    Q, M = (0, 'Q'), (1, 'M')
    H = lambda s: (0, 'H', s)
    K = lambda s: (1, 'K', s)

    G = Graph(multiedges=False, loops=False)
    triples = pg2_triples(F)
    G.add_vertices([(0,) + t for t in triples] + [(1,) + t for t in triples] +
                   [Q, M] + [H(s) for s in S] + [K(s) for s in S])

    # (C1) all incidences of PG(2,q) (u x + v y + w z = 0) ...
    removed = set()
    for p in triples:
        for L in triples:
            if sum(p[i] * L[i] for i in range(3)) == 0:
                G.add_edge((0,) + p, (1,) + L)
    #      ... except the flags (X_s, lam_s), s in S: for four hats all four are deleted, for three
    #      hats only (X_a, lam_a) is (for T = {0,1} the rotation is the identity).
    for s in (S if not three_hats else [a]):
        G.delete_edge(X(s), lam(s))
    #      ... and the rotation: X_t is put on lam_sigma(t), t in T (X_0 on lam_c, X_c on lam_1,
    #      X_1 on lam_0).  Three hats: no rotation.
    for t in sigma:
        G.add_edge(X(t), lam(sigma[t]))

    for s in S:
        for w in els:
            # (C2) the hat point H_s lies on the line [w:1:-s] for every w: these are the q lines of
            #      PG(2,q) through X_s other than ell (lam_s is the one with w = 0).
            G.add_edge(H(s), ln(w, 1, -s))
            # (C3) the hat line K_s contains the point (x:s:1) for every x: these are the q points
            #      of lam_s other than A (X_s is the one with x = 0).
            G.add_edge(pt(w, s, 1), K(s))

    # (C4) M contains P, the points X_t with t not in T, and every hat point H_s.
    G.add_edge(P, M)
    for t in els:
        if t not in T:
            G.add_edge(X(t), M)
    for s in S:
        G.add_edge(H(s), M)
    # (C5) Q lies on lam_inf, on the lines lam_t with t not in T, and on every hat line K_s.
    G.add_edge(Q, lam_inf)
    for t in els:
        if t not in T:
            G.add_edge(Q, lam(t))
    for s in S:
        G.add_edge(Q, K(s))

    # (C6) the links.
    G.add_edge(A, K(a))                                # A lies on K_a
    G.add_edge(H(a), ell)                              # H_a lies on ell
    if three_hats:
        G.add_edge(H(zero), K(one))                    # H_0 on K_1 and H_1 on K_0 (pi = (0 1))
        G.add_edge(H(one), K(zero))
    else:
        for t in T:
            G.add_edge(H(t), K(sigma[t]))              # H_0 on K_c, H_c on K_1, H_1 on K_0

    # (C7) optional filler: every point of degree q+1 is joined to the line delta(p), where
    #      delta(x:y:z) = [x:z:-y] (a correlation of PG(2,q), so p is not on delta(p)).
    if filler:
        low = [v for v in G.vertices(sort=False) if v[0] == 0 and G.degree(v) == q + 1]
        for v in low:
            x, y, z = v[1:]
            L = ln(x, z, -y)
            assert not G.has_edge(v, L)
            G.add_edge(v, L)
    return G


def build_d3_three_hats(q, a=None, filler=False, F=None):
    """The Araujo-Pardo--Lopez structure (three hats), for comparison; same labels as above."""
    return build_d3_four_hats(q, a=a, c=None, filler=filler, F=F, three_hats=True)


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


def check(q):
    """Builds the four-hat graph for GF(q) (core and with the filler) and compares with the theorem:
    2(q^2+q+6) vertices, maximum degree q+2, bipartite, diameter 3; the filled graph is (q+2)-regular."""
    ok = True
    G = build_d3_four_hats(q)
    ok &= report(G, 2 * (q * q + q + 6), q + 2, 3, name=f'four hats, q={q}, core')
    R = build_d3_four_hats(q, filler=True)
    ok &= report(R, 2 * (q * q + q + 6), q + 2, 3, name=f'four hats, q={q}, with filler')
    ok &= (min(R.degree()) == q + 2)
    print(f'   filled graph is {q+2}-regular: {min(R.degree()) == q + 2}')
    return ok


# `sage d3_four_hats.sage` runs the checks; to only load the functions, set NO_AUTO_CHECK = True first.
if 'NO_AUTO_CHECK' not in globals():
    for q_ in (4, 5):
        assert check(q_)
