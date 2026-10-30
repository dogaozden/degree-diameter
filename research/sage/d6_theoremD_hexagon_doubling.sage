r"""
Diameter 6: Theorem D (SYNTHETIC.md section 3, Theorem 3.3).  The split Cayley hexagon H(q), a Hermitian spread Sigma, a line v of
Sigma, an exact whisker set W, and Delorme's doubling with levels A_2 = {v}, A_1, A_0 (section 3.3).  Also Theorem R (section 3.4),
the regular version, as build_d6_theoremR.
Run:   sage d6_theoremD_hexagon_doubling.sage            (checks q = 2 (m = 2, 3) and q = 3 (m = 2); then Theorem R for both)
       sage -c 'NO_AUTO_CHECK=True; load("d6_theoremD_hexagon_doubling.sage"); G = build_d6_theoremD(4); print(G.order())'

Vertex labels: the elements of H(q) as in hexagon.sage -- (0, x0..x6) a point, (1, <rref of 2x7>) a line -- followed by the WORD that
indexes the version, so a vertex is (0, x0..x6, w) or (1, r.., w) with w a tuple of letters in {0,..,m-1}; its length is level+1
(the empty word () for the elements of level -1, which are not doubled).  Examples: (1, ..., (i,j,k)) is a version v^{ijk} of v.

Notation (SYNTHETIC.md 3.2, 3.3):
  Sigma  the Hermitian spread: the q^3+1 lines of H(q) inside the hyperplane Pi (x0 + c x4 = 0, q odd; x3 = x0 + c x4, q even)
  P_Sigma = the points of Pi (on exactly one line of Sigma);  v = the line through e1 = (0:1:0:0:0:0:0) and e6 = (0:0:0:0:0:0:1)
  free points: points not in P_Sigma at distance 5 from v (q^3(q^2-1) of them)
  whisker: a line opposite v, not in Sigma (it has one point in P_Sigma and q free points); W an exact whisker set
           (every free point on exactly one whisker), q^2(q^2-1) lines:
           q odd: W = { lines m != v with all points in some Pi_{al,be}, (al,be) != 0, nu(m cap Pi) = F(al,be) }  (POLISHED.md Theorem 6.5)
           q even: the same with the formula of POLISHED.md Theorem 6.14;  q = 2: found by an exact-cover search (Sage dancing links)
  levels: v is at level 2; the other lines of Sigma and the points of v at level 1; the other points of P_Sigma, the q(q+1) lines
          meeting v, and the whiskers at level 0; everything else (level -1) is not doubled.
"""
import itertools, random

if 'hexagon' not in globals():
    # find hexagon.sage next to this file (or in the current directory, or one level up)
    import os
    _dirs = [os.getcwd(), os.path.join(os.getcwd(), '..'), os.path.dirname(os.path.abspath(globals().get('__file__', 'x')))]
    _path = next(os.path.join(d, 'hexagon.sage') for d in _dirs if os.path.exists(os.path.join(d, 'hexagon.sage')))
    _saved = globals().get('NO_AUTO_CHECK', None)
    NO_AUTO_CHECK = True
    load(_path)
    if _saved is None:
        del NO_AUTO_CHECK


# --------------------------------------------------------------------------------------------
# the configuration: spread, v, free points, whiskers
# --------------------------------------------------------------------------------------------

def d6_configuration(H, whiskers=None, params=None):
    r"""
    Returns a dictionary with the Hermitian spread and everything of section 3.2 for the hexagon H = hexagon(q):
      c, Spts, spread, v, Pv, Lv (lines != v meeting v), free, cand (lines opposite v not in the spread), W.
    whiskers: optionally a list of line labels to use as the whisker set instead of computing one (it is checked to be exact).
    params:   optionally (c0, c1) for the whisker formula (default: the first pair, in the order of the field, with G zero-free).
    """
    q, F = H.q, H.F
    c, Spts, spread = hermitian_spread(H)
    v = line_v(H)
    assert v in spread
    G = H.graph()
    dist_v = G.shortest_path_lengths(v)
    Pv = set(H.pts_on[v])
    Lv = [L for p in Pv for L in H.lines_on[p] if L != v]
    sset = set(spread)
    free = {p for p in H.points if p not in Spts and dist_v[p] == 5}
    assert len(free) == q ** 3 * (q * q - 1)
    cand = [L for L in H.lines if dist_v[L] == 6 and L not in sset]       # lines opposite v, not in Sigma
    if whiskers is not None:
        W = list(whiskers)
    elif q == 2:
        W = whiskers_exact_cover(H, free, cand)
    else:
        W = whiskers_formula(H, c, v, Spts, params)
    W = sorted(W, key=lambda t: [str(a) for a in t])
    # W is exact: q^2(q^2-1) whiskers, every free point on exactly one
    assert len(W) == q * q * (q * q - 1)
    assert all(sum(1 for L in H.lines_on[p] if L in set(W)) == 1 for p in free)
    assert set(W) <= set(cand)
    return dict(c=c, Spts=Spts, spread=spread, v=v, Pv=Pv, Lv=Lv, free=free, cand=cand, W=W, dist_v=dist_v)


def whiskers_exact_cover(H, free, cand):
    """q = 2: an exact cover of the free points by whiskers (each candidate line covers its q free points), by dancing links."""
    from sage.combinat.matrices.dancing_links import dlx_solver
    fl = sorted(free, key=lambda t: [str(a) for a in t])
    col = {p: i for i, p in enumerate(fl)}
    rows = [[col[p] for p in H.pts_on[L] if p in col] for L in cand]
    sol = dlx_solver(rows).one_solution()
    assert sol is not None, 'no exact whisker set'
    return [cand[i] for i in sol]


def whisker_G(F, al, be, c, c0, c1):
    """The polynomial G of POLISHED.md Lemma 6.4 (q odd) / 6.11 (q even); c is the constant of Pi."""
    if F.characteristic() == 2:
        return (c0 * al + c1 * be) * (al * al + al * be + c * be * be) + be ** 3
    return (c0 * al + c1 * be) * (al * al + c * be * be) - be ** 3


def whiskers_formula(H, c, v, Spts, params=None):
    r"""
    The exact whisker set of POLISHED.md Theorem 6.5 (q odd) / Theorem 6.14 (q even):
      W = { lines m != v : m lies in some hyperplane Pi_{al,be} with (al,be) != (0,0), and nu(X) = F(al,be) },
    where X = the unique point of m in Pi, nu(X) = num/den and F(al,be) = G(al,be)/(al^2 + c be^2)  [q even: al^2 + al be + c be^2]
    with  q odd:  num = x2 x3 - x4 x5,  den = c x2^2 + x5^2;   q even:  num = x2 x3 + x2 x4 + x4 x5,  den = c x2^2 + x2 x5 + x5^2.
    The constants (c0, c1) are chosen so that G has no zero on GF(q)^2 minus 0.
    """
    F = H.F
    q = H.q
    els = list(F)
    nz = [(a, b) for a in els for b in els if (a, b) != (0, 0)]
    if params is None:
        params = next((c0, c1) for c0 in els for c1 in els
                      if (F.characteristic() != 2 or c0 != 0) and all(whisker_G(F, a, b, c, c0, c1) != 0 for a, b in nz))
    c0, c1 = params
    assert all(whisker_G(F, a, b, c, c0, c1) != 0 for a, b in nz), 'G has a zero'
    W = []
    for (al, be) in nz:
        quad = al * al + al * be + c * be * be if F.characteristic() == 2 else al * al + c * be * be
        for L in H.lines:
            if L == v:
                continue
            if not all(in_Pi(F, c, p, al, be) for p in H.pts_on[L]):
                continue
            Xs = [p for p in H.pts_on[L] if in_Pi(F, c, p)]
            assert len(Xs) == 1
            x = Xs[0][1:]
            if F.characteristic() == 2:
                num, den = x[2] * x[3] + x[2] * x[4] + x[4] * x[5], c * x[2] ** 2 + x[2] * x[5] + x[5] ** 2
            else:
                num, den = x[2] * x[3] - x[4] * x[5], c * x[2] ** 2 + x[5] ** 2
            if num / den == whisker_G(F, al, be, c, c0, c1) / quad:
                W.append(L)
    return W


def d6_levels(H, conf):
    """The levels of section 3.3: v at level 2; Sigma\\{v} and the points of v at level 1; P_Sigma\\P_v, the lines meeting v and
    the whiskers at level 0.  Elements not in the dictionary have level -1."""
    level = {}
    for x in list(conf['spread']) + list(conf['Spts']) + list(conf['Lv']) + list(conf['W']):
        level[x] = 0
    for x in list(conf['spread']) + list(conf['Pv']):
        level[x] = 1
    level[conf['v']] = 2
    return level


# --------------------------------------------------------------------------------------------
# the doubling with levels
# --------------------------------------------------------------------------------------------

def words(m, k):
    return list(itertools.product(range(m), repeat=k))


def double_levels_generic(H, level, m):
    """Definition 3.1: x^w I y^u iff x I y in H and one of the words w, u is a prefix of the other."""
    G = Graph(multiedges=False, loops=False)
    ver = lambda x: [x + (w,) for w in words(m, level.get(x, -1) + 1)]
    for x in H.points + H.lines:
        G.add_vertices(ver(x))
    for L in H.lines:
        for p in H.pts_on[L]:
            for vp in ver(p):
                for vl in ver(L):
                    a, b = vp[-1], vl[-1]
                    if a[:len(b)] == b[:len(a)]:
                        G.add_edge(vp, vl)
    return G


def build_d6_theoremD(q, m=2, whiskers=None, params=None, H=None, conf=None):
    r"""
    The Sage Graph of the doubled hexagon of Theorem D (SYNTHETIC.md 3.3): 2N + (m-1)(2q^4+2q^3+2q+2+m(q^3+q+2)+m^2)
    vertices, maximum degree q+m, diameter 6.  The edges are written block by block, following the table of 3.3
    (i, j, k are letters in {0,..,m-1}; a vertex x^w is the label of x followed by the word w).
    """
    H = H if H is not None else hexagon(q)
    conf = conf if conf is not None else d6_configuration(H, whiskers=whiskers, params=params)
    v, Pv, Lv, W, Spts, spread = conf['v'], conf['Pv'], conf['Lv'], conf['W'], conf['Spts'], conf['spread']
    level = d6_levels(H, conf)
    sset, Wset, Lvset = set(spread), set(W), set(Lv)
    ver = lambda x: [x + (w,) for w in words(m, level.get(x, -1) + 1)]
    G = Graph(multiedges=False, loops=False)
    for x in H.points + H.lines:
        G.add_vertices(ver(x))                                  # the versions: m^(level+1) of each element

    # (1) level 2: v^{ijk} is on p^{ij} for the q+1 points p of v
    for w in words(m, 3):
        for p in H.pts_on[v]:
            G.add_edge(v + (w,), p + (w[:2],))
    # (2) level 1, a point p of v: p^{ij} is on v^{ij1}..v^{ijm} (all m versions of v above it) and on L^i for the q other lines
    #     L != v through p (L meets v, so it is in Lv at level 0, word i)
    for p in Pv:
        for w in words(m, 2):
            for k in range(m):
                G.add_edge(p + (w,), v + (w + (k,),))
            for L in H.lines_on[p]:
                if L != v:
                    G.add_edge(p + (w,), L + (w[:1],))
    # (3) level 1, a spread line n != v: n^{ij} is on p^i for the q+1 points p of n (they are in P_Sigma, level 0, word i)
    for n in spread:
        if n != v:
            for w in words(m, 2):
                for p in H.pts_on[n]:
                    G.add_edge(n + (w,), p + (w[:1],))
    # (4) level 0, a point p of P_Sigma not on v: p^i is on n^{i1}..n^{im} for its spread line n, on h^i for each whisker h through p,
    #     and on every other line through p (level -1, not doubled)
    for p in Spts:
        if p in Pv:
            continue
        for w in words(m, 1):
            for L in H.lines_on[p]:
                if L in sset:
                    for k in range(m):
                        G.add_edge(p + (w,), L + (w + (k,),))
                elif L in Wset:
                    G.add_edge(p + (w,), L + (w,))
                else:
                    G.add_edge(p + (w,), L + ((),))
    # (5) level 0, a line L != v meeting v at p0: L^i is on p0^{i1}..p0^{im} and on the other q points of L (level -1)
    for L in Lv:
        p0 = next(p for p in H.pts_on[L] if p in Pv)
        for w in words(m, 1):
            for k in range(m):
                G.add_edge(L + (w,), p0 + (w + (k,),))
            for x in H.pts_on[L]:
                if x != p0:
                    G.add_edge(L + (w,), x + ((),))
    # (6) level 0, a whisker h: h^i is on p^i for its point p in P_Sigma and on its q free points (level -1)
    for h in W:
        p0 = next(p for p in H.pts_on[h] if p in Spts)
        for w in words(m, 1):
            G.add_edge(h + (w,), p0 + (w,))
            for x in H.pts_on[h]:
                if x != p0:
                    G.add_edge(h + (w,), x + ((),))
    # (7) level -1, a point r outside P_Sigma: r is on all m versions of the line through r meeting v, or of the whisker through r,
    #     and on every other line through r (level -1)
    # (8) level -1, a line N outside A_0: N is on all m versions of its point in P_Sigma, and on its q other points (level -1)
    for L in H.lines:
        if level.get(L, -1) == -1:
            for x in H.pts_on[L]:
                if level.get(x, -1) == -1:
                    G.add_edge(L + ((),), x + ((),))                # (7)/(8): old incidences between two elements of level -1
                else:
                    for w in words(m, level[x] + 1):                # (8)/(7): the one element of A_0 on N, all its versions
                        G.add_edge(L + ((),), x + (w,))
    return G


def expected_d6(q, m):
    N = (q + 1) * (q ** 4 + q ** 2 + 1)
    return 2 * N + (m - 1) * (2 * q ** 4 + 2 * q ** 3 + 2 * q + 2 + m * (q ** 3 + q + 2) + m * m)


# --------------------------------------------------------------------------------------------
# Theorem R: the regular version (section 3.4)
# --------------------------------------------------------------------------------------------

def build_d6_theoremR(q, m=2, seed=5, H=None, conf=None, whiskers=None, params=None):
    r"""
    The regular structure of Theorem R.  Starting from the doubling D of Theorem D:
      repeated lines: the m versions n^{i1..im} of a spread line n != v have the same points, and so do the m versions v^{ij1..ijm};
      delete (m-1)m(q^3-q+m) such lines: the versions v^{ijk} with k >= 1, and n^{ij} with j >= 1 for all spread lines n != v
      except q of them (the first q spread lines other than v in the order of hexagon.sage);
      then complete to (q+m)-regularity by one anti-flag for each missing incidence; the existence of such a set is Lemma 7.2 of
      POLISHED.md (swap argument).  The anti-flags are not given by a rule: here they come from a random swap procedure with
      the given seed.   Order: 2(q+1)(q^4+q^2+1+(m-1)(q^3+m+1)).
    """
    H = H if H is not None else hexagon(q)
    conf = conf if conf is not None else d6_configuration(H, whiskers=whiskers, params=params)
    D = build_d6_theoremD(q, m, H=H, conf=conf)
    v, spread = conf['v'], conf['spread']
    Sv = [n for n in spread if n != v]
    keep = set(Sv[:q])
    delete = []
    for L in H.lines:
        if L == v:
            delete += [L + (w,) for w in words(m, 3) if w[2] >= 1]               # v^{ijk}, k >= 1
        elif L in set(Sv) and L not in keep:
            delete += [L + (w,) for w in words(m, 2) if w[1] >= 1]               # n^{ij}, j >= 1
    assert len(delete) == (m - 1) * m * (q ** 3 - q + m)
    D.delete_vertices(delete)
    Delta = q + m
    sides = {0: [x for x in D.vertices(sort=False) if x[0] == 0], 1: [x for x in D.vertices(sort=False) if x[0] == 1]}
    assert len(sides[0]) == len(sides[1])
    ptsl = sorted(sides[0], key=str)
    lnsl = sorted(sides[1], key=str)
    P = [p for p in ptsl for _ in range(Delta - D.degree(p))]
    Ls = [L for L in lnsl for _ in range(Delta - D.degree(L))]
    assert len(P) == len(Ls)
    rng = random.Random(int(seed))
    rng.shuffle(Ls)
    J = list(zip(P, Ls))
    for it in range(200000):                                 # swap the line parts of two pairs until all pairs are anti-flags
        cnt = {}
        for e in J:
            cnt[e] = cnt.get(e, 0) + 1
        badi = [i for i in range(len(J)) if D.has_edge(*J[i]) or cnt[J[i]] > 1]
        if not badi:
            break
        i = rng.choice(badi)
        j = rng.randrange(len(J))
        (p, L), (p2, L2) = J[i], J[j]
        J[i], J[j] = (p, L2), (p2, L)
    else:
        raise RuntimeError('no completion found')
    D.add_edges(J)
    return D


# --------------------------------------------------------------------------------------------
# check
# --------------------------------------------------------------------------------------------

def report(G, expect_n, expect_deg, expect_diam, bip=True, name='', regular=False):
    n = G.order()
    maxdeg = max(G.degree())
    isbip = G.is_bipartite()
    diam = G.diameter()
    ok = (n == expect_n and maxdeg == expect_deg and isbip == bip and diam == expect_diam)
    if regular:
        ok = ok and min(G.degree()) == expect_deg
    print(f'{name}: vertices {n} (expected {expect_n}), max degree {maxdeg} (expected {expect_deg}), '
          f'bipartite {isbip}, diameter {diam} (expected {expect_diam})' + (f', min degree {min(G.degree())}' if regular else '')
          + f'  ->  {"OK" if ok else "MISMATCH"}')
    return ok


def check(q, m=2, regular=True):
    """Theorem D (and Theorem R if regular) for H(q) and m: vertices, max degree q+m, bipartite, diameter 6.  Also
    compares the block-by-block edge list with the generic definition 3.1 of the doubling."""
    H = hexagon(q)
    conf = d6_configuration(H)
    print(f'H({q}): N = {H.N}, |Sigma| = {len(conf["spread"])}, free points {len(conf["free"])}, |W| = {len(conf["W"])}, '
          f'c = {conf["c"]}')
    G = build_d6_theoremD(q, m, H=H, conf=conf)
    ok = report(G, expected_d6(q, m), q + m, 6, name=f'Theorem D, q={q}, m={m}')
    G2 = double_levels_generic(H, d6_levels(H, conf), m)
    same = set(map(frozenset, G.edges(labels=False, sort=False))) == set(map(frozenset, G2.edges(labels=False, sort=False)))
    print(f'   block-by-block edges equal the generic definition 3.1: {same}')
    ok &= same
    if regular and m == 2:
        R = build_d6_theoremR(q, m, H=H, conf=conf)
        ok &= report(R, 2 * (q + 1) * (q ** 4 + q ** 2 + 1 + (m - 1) * (q ** 3 + m + 1)), q + m, 6,
                     name=f'Theorem R, q={q}, m={m}', regular=True)
    return ok


if 'NO_AUTO_CHECK' not in globals():
    assert check(2, 2)
    assert check(2, 3, regular=False)
    assert check(3, 2)
