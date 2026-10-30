r"""
Diameter 3, the (16,3) record on 396 vertices: PG(2,13) with three disjoint four-hat gadgets,
placed on three anti-flags that are images of each other under the order-3 subgroup of the Singer cycle.
(research/d3d6/REPORT.md; frames in research/d3d6/graphs/sym3_q13_frames.json; the graph is
research/d3d6/graphs/sym3_q13_d16_n396.json.)

Run:   sage d3_16_three_gadgets.sage

The record = PG(2,13) + three gadgets + the three edges Q_{g+1} ~ M_g (step R7 below).

Vertex labels (0 = point side, 1 = line side), g = 0, 1, 2 the number of the gadget:
    (0, x, y, z)      the point (x:y:z) of PG(2,13), first nonzero coordinate 1
    (1, u, v, w)      the line [u:v:w], first nonzero coordinate 1;  (x:y:z) on [u:v:w] iff ux+vy+wz = 0
    (0, 'Q', g)       the point Q of gadget g          (1, 'M', g)    the line M of gadget g
    (0, 'H', g, s)    the hat point H_s of gadget g    (1, 'K', g, s) the hat line K_s of gadget g,  s in {0,1,'a','c'}

One gadget is the four-hat gadget of d3_four_hats.sage (SYNTHETIC.md section 1.2, Definition 1.1 with
S = {0,1,a,c}, pi = rho = sigma = (0 c 1)) written for an arbitrary frame (A, ell, X_0, X_1, X_a, X_c):
A a point, ell a line not through A, and four points X_s of ell.  lam_s = A X_s is the line joining A and X_s.
The coordinates of the plane are the ones coming from the Singer cycle: the point number i of
Z_183 is w^i, w a primitive element of GF(13^3), in coordinates (c_0 : c_1 : c_2) with
w^i = c_0 + c_1 w + c_2 w^2; the line number j is D + j, where D = {i : c_2(w^i) = 0}.  The translation
i -> i + 61 (j -> j + 61 on lines) is a collineation of order 3; the three frames are one frame and its
two translates.
"""
import itertools


def normalize(v):
    for x in v:
        if x != 0:
            inv = ~x
            return tuple(inv * y for y in v)
    raise ValueError('zero vector')


# --------------------------------------------------------------------------------------------
# PG(2,q) from a Singer cycle (q prime)
# --------------------------------------------------------------------------------------------

def singer_plane(q):
    r"""
    PG(2,q) with its Singer cycle, q prime.  Returns a dictionary with
      F      GF(q)
      n      q^2+q+1
      pt[i]  the label (0, x, y, z) of the point number i,  i in Z_n
      ln[j]  the label (1, u, v, w) of the line  number j,  j in Z_n
      on[j]  the set of numbers i of the points on line j (= the translate D + j of the difference set D)
    The primitive cubic is the first x^3 + a x^2 + b x + c (in the order of (a,b,c) in {0..q-1}^3)
    with root w of order q^3 - 1; this is the cubic used by research/d3d6/singer.py.
    """
    F = GF(q)
    R = PolynomialRing(F, 'x')
    xx = R.gen()
    n = q * q + q + 1
    for a, b, c in itertools.product(range(q), repeat=3):
        f = xx ** 3 + a * xx ** 2 + b * xx + c
        if c == 0 or not f.is_irreducible():
            continue
        E = GF(q ** 3, 'w', modulus=f)
        w = E.gen()
        if w.multiplicative_order() != q ** 3 - 1:
            continue
        pw = [list((w ** i)) for i in range(q ** 3 - 1)]          # coefficients (c0, c1, c2) of w^i
        D = sorted({i % n for i in range(q ** 3 - 1) if pw[i][2] == 0})
        assert len(D) == q + 1
        pt = [(0,) + normalize(tuple(F(t) for t in pw[i])) for i in range(n)]
        # the line D + j is the kernel of the functional  u -> c_2(w^(-j) u)  on GF(q)^3 = GF(q^3);
        # its coordinates are the values of the functional on 1, w, w^2.
        ln = []
        for j in range(n):
            func = tuple(F((w ** (k - j)).list()[2]) for k in range(3))
            ln.append((1,) + normalize(func))
        on = [frozenset((d + j) % n for d in D) for j in range(n)]
        for j in range(n):                                          # coordinates agree with the Singer model
            for i in range(n):
                dot = sum(pt[i][1 + k] * ln[j][1 + k] for k in range(3))
                assert (dot == 0) == (i in on[j])
        return dict(F=F, n=n, pt=pt, ln=ln, on=on, E=E, w=w)
    raise ValueError('no primitive cubic')


# --------------------------------------------------------------------------------------------
# the four-hat gadget on an arbitrary frame
# --------------------------------------------------------------------------------------------

def build_d3_gadgets(plane, frames, cross=True):
    r"""
    The incidence graph of the plane with one four-hat gadget per frame.
    plane   the dictionary of singer_plane(q)
    frames  a list of frames (A, ell, [X_0, X_1, X_a, X_c]) of point/line NUMBERS (A a point number,
            ell a line number, the X_s point numbers of ell); gadget g is built on frames[g].
    The edge set is  (plane flags  minus  all deleted flags)  plus  all added flags, as in
    research/d3d6/multi_gadget.py, so the gadgets are independent of each other.
    cross   if True (the record), finish with the "greedy step": Q of gadget g+1 is joined to M of
            gadget g (g mod the number of gadgets).  Each Q and M has degree q+2 = 15 in its own
            gadget (spare capacity 1 at Delta = 16), so these 3 edges keep the maximum degree 16.
            Without them the graph has the right degrees but diameter 4.
    """
    pt, ln, on, n = plane['pt'], plane['ln'], plane['on'], plane['n']
    lines_of = [[j for j in range(n) if i in on[j]] for i in range(n)]            # lines through point i

    def join(i, k):                                                              # the line through two points
        return next(j for j in lines_of[i] if k in on[j])

    G = Graph(multiedges=False, loops=False)
    G.add_vertices(pt + ln)
    flags = {(i, j) for j in range(n) for i in on[j]}                            # (a) the plane PG(2,q)
    removed, added = set(), set()
    new_edges = []                                                               # edges among new vertices
    for g, (A, ell, X) in enumerate(frames):
        X0, X1, Xa, Xc = X
        S = {0: X0, 1: X1, 'a': Xa, 'c': Xc}
        Q, M = (0, 'Q', g), (1, 'M', g)
        H = lambda s: (0, 'H', g, s)
        K = lambda s: (1, 'K', g, s)
        lam = {s: join(A, S[s]) for s in S}                                      # lam_s = A X_s
        G.add_vertices([Q, M] + [H(s) for s in S] + [K(s) for s in S])
        # R1: delete the four flags (X_s, lam_s) ...
        for s in S:
            removed.add((S[s], lam[s]))
        #     ... and add the rotation (X_0 on lam_c, X_c on lam_1, X_1 on lam_0)
        for t, u in ((0, 'c'), ('c', 1), (1, 0)):
            added.add((S[t], lam[u]))
        for s in S:
            # R2: H_s lies on every line through X_s other than ell (q lines, lam_s among them)
            for j in lines_of[S[s]]:
                if j != ell:
                    new_edges.append((H(s), ln[j]))
            # R3: K_s contains every point of lam_s other than A (q points, X_s among them)
            for i in on[lam[s]]:
                if i != A:
                    new_edges.append((pt[i], K(s)))
        # R4: M contains the points of ell other than X_0, X_1, X_c (so X_a and the unmarked ones)
        # R5: Q lies on the lines A X for the same points X
        for i in on[ell]:
            if i not in (X0, X1, Xc):
                new_edges.append((pt[i], M))
                new_edges.append((Q, ln[join(A, i)]))
        for s in S:
            new_edges.append((H(s), M))             # R4: M contains every hat point H_s
            new_edges.append((Q, K(s)))             # R5: Q lies on every hat line K_s
        # R6: the links
        new_edges.append((pt[A], K('a')))           # A lies on K_a
        new_edges.append((H('a'), ln[ell]))         # H_a lies on ell
        new_edges.append((H(0), K('c')))            # H_0 on K_c
        new_edges.append((H('c'), K(1)))            # H_c on K_1
        new_edges.append((H(1), K(0)))              # H_1 on K_0
    # the sets "added"/"removed" use point/line numbers; K(s) etc are labels
    for (i, j) in (flags - removed) | added:
        G.add_edge(pt[i], ln[j])
    G.add_edges(new_edges)
    # R7: the finishing step of the record: Q of gadget g+1 on M of gadget g (indices mod number of gadgets);
    #     these are the only edges between two different gadgets.
    if cross:
        k = len(frames)
        for g in range(k):
            G.add_edge((0, 'Q', (g + 1) % k), (1, 'M', g))
    return G


def frames_16_3():
    """The three frames of the record (A, ell, [X_0, X_1, X_a, X_c]) as numbers in Z_183:
    the frame (0, 38, [9, 30, 120, 124]) and its two translates by 61 (research/d3d6/graphs/sym3_q13_frames.json)."""
    n, s3 = 183, 61
    base = (0, 38, [9, 30, 120, 124])
    return [((base[0] + t) % n, (base[1] + t) % n, [(x + t) % n for x in base[2]]) for t in (0, s3, 2 * s3)]


def build_d3_16_three_gadgets():
    plane = singer_plane(13)
    return build_d3_gadgets(plane, frames_16_3())


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


def check(q=13):
    assert q == 13, 'the frames are for PG(2,13)'
    G = build_d3_16_three_gadgets()
    print('degrees:', sorted(set(G.degree())), ' edges:', G.size())
    ok = report(G, 2 * 183 + 3 * 10, 16, 3, name='(16,3), PG(2,13) + three four-hat gadgets + 3 cross edges')
    H = build_d3_gadgets(singer_plane(13), frames_16_3(), cross=False)
    print('without the 3 cross edges: edges', H.size(), ' diameter', H.diameter(), '(the cross edges are needed)')
    return ok


if 'NO_AUTO_CHECK' not in globals():
    assert check(13)
