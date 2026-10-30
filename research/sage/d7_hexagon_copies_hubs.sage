r"""
Diameter 7: 2r+1 copies of the split Cayley hexagon H(q) (or of its dual), joined by matchings, with freed sets and hubs
(SYNTHETIC.md section 4; research/theorems/D7_HEXAGON.md; reference builder research/synthetic/conics2/typed_build.py,
small example research/synthetic/checks/check_d7.py).   GENERAL BUILDER; CHECKED ONLY FOR q = 2, 3
(the records are q = 7,...,17 with 10^6-10^8 vertices; they are not built here).

Run (from the directory research/sage/):   sage d7_hexagon_copies_hubs.sage
Needs hexagon.sage (same directory).

The construction in this file's words (SYNTHETIC.md 4.1, 4.2):
  * levels: L = 2r+1 copies Gamma_0..Gamma_{L-1} of H(q); each copy has a TYPE, 'H' (a copy of H(q): its points are points of
    the structure) or 'D' (a copy of the dual hexagon: the lines of H(q) are the points of the structure).
  * transitions: for every copy j and k = 1..r a bijection M_{j,k} from the points of copy j (structure points) onto the
    lines of copy j+k (structure lines); p is incident with M_{j,k}(p).   Types: H->D and D->H transitions are FRIENDLY
    (the matching is the identity of H(q): a point of H(q) in an H copy to the same point in a D copy, where it is a line);
    H->H transitions use a bijection sigma from the points of H(q) to its lines, D->D transitions use sigma^-1.
  * freed sets: on a transition the matching incidences p ~ M(p) are DELETED for p in a freed set R.  Friendly H->D: R = the
    point set of the Hermitian spread (a segment set); friendly D->H: R = the lines meeting the spread line v plus an exact
    set of whiskers (a dual segment set); H->H: a set R' of pairwise opposite points with sigma a local duality at R'
    (D->D: sigma(R'), with sigma^-1).  Theorems 4.5 and 4.6 say the transition is then still repaired.
  * hubs: a LINE-hub (a new line of the structure) takes one slot (a deleted incidence) at a freed structure point in EVERY copy;
    a POINT-hub takes one slot at a freed structure line in every copy; hub h takes the h-th slot of each level.
    A hub graph joins line-hubs to point-hubs (degree <= q - r).  Theorem 4.3: the diameter is 7.
  * all degrees are at most Delta = q + 1 + r; vertices: 2N L + (number of hubs), N = (q+1)(q^4+q^2+1).

Vertex labels (first entry 0 = point side of the structure, 1 = line side):
    (s, 'copy', j, h)      element h of copy j; h = (0, x0..x6) is a point of H(q), h = (1, ...) a line of H(q) (labels of
                           hexagon.sage).  s = 0 for the points of H(q) in an 'H' copy and for the lines of H(q) in a 'D' copy,
                           s = 1 for the others.
    (1, 'hub', h)          line-hub number h        (0, 'hub', h)   point-hub number h
"""
import itertools
import os

# ---- load the hexagon helper (no self-test)
_had_flag = 'NO_AUTO_CHECK' in globals()
NO_AUTO_CHECK = True
_here = os.path.dirname(os.path.abspath(globals().get('__file__', 'd7_hexagon_copies_hubs.sage')))
for _p in (os.path.join(_here, 'hexagon.sage'), 'hexagon.sage'):
    if os.path.exists(_p):
        load(_p)
        break
else:
    raise IOError('hexagon.sage not found: run from research/sage/')
if not _had_flag:
    del NO_AUTO_CHECK


# --------------------------------------------------------------------------------------------
# freed sets: the Hermitian spread, the lines meeting v, the exact whisker set
# --------------------------------------------------------------------------------------------

def whisker_parameters(F):
    r"""(c, c0, c1) of POLISHED.md Lemma 6.4 (q odd): c with -c a non-square, and c0, c1 such that
    G(a,b) = (c0 a + c1 b)(a^2 + c b^2) - b^3 has no zero on F^2 minus 0;  q even (Lemma 6.11): (c, c0, c1) with Tr(c) = 1 and
    G(a,b) = (c0 a + c1 b)(a^2 + a b + c b^2) + b^3 zero-free.  First solution in the order of the list of F
    (the same search as research/synthetic/conics2/typed_build.py)."""
    els = list(F)
    pairs = [(a, b) for a in els for b in els if a != 0 or b != 0]
    if F.characteristic() == 2:
        cands = [d for d in els if d != 0 and trace_to_prime(F, d) == 1]
        G = lambda c, c0, c1, a, b: (c0 * a + c1 * b) * (a * a + a * b + c * b * b) + b ** 3
    else:
        sq = {x * x for x in els if x != 0}
        cands = [c for c in els if c != 0 and -c not in sq]
        G = lambda c, c0, c1, a, b: (c0 * a + c1 * b) * (a * a + c * b * b) - b ** 3
    for c in cands:
        for c0 in els:
            for c1 in els:
                if all(G(c, c0, c1, a, b) != 0 for a, b in pairs):
                    return c, c0, c1
    raise ValueError('no parameters')


def friendly_sets(H):
    r"""
    The freed sets of the friendly transitions (typed_build.friendly_sets):
      R_H  the points of the Hermitian spread S (the lines of H(q) inside the hyperplane Pi), a segment set;
      R_L  the lines != v meeting the spread line v (q(q+1) of them), together with the exact whisker set W of POLISHED.md
           Theorem 6.5 (q odd) or 6.14 (q even): q^2(q^2-1) lines opposite v, no two through a free point, every free point on one.
           |R_L| = q(q^3+1); it is a dual segment set.
    Returns (RH, RL, S, v) with RH a set of point labels, RL a set of line labels, S the list of spread lines.
    """
    F, q = H.F, H.q
    c, c0, c1 = whisker_parameters(F)
    even = F.characteristic() == 2
    in_Pi_z = lambda p, al, be: in_Pi(F, c, p, al, be)
    S = [Ln for Ln in H.lines if all(in_Pi_z(p, 0, 0) for p in H.pts_on[Ln])]
    assert len(S) == q ** 3 + 1
    v = line_v(H)
    assert v in S
    # nu(x) = num/den on the points of Pi (0 where den = 0, as in typed_build)
    def nu(p):
        x = p[1:]
        if even:
            num = x[2] * x[3] + x[2] * x[4] + x[4] * x[5]
            den = c * x[2] ** 2 + x[2] * x[5] + x[5] ** 2
        else:
            num = x[2] * x[3] - x[4] * x[5]
            den = c * x[2] ** 2 + x[5] ** 2
        return num / den if den != 0 else F(0)
    W = set()
    for al in F:
        for be in F:
            if al == 0 and be == 0:
                continue
            # S_z: the Hermitian-type spread of the hyperplane Pi_z : x0 + c x4 + al x2 + be x5 = 0; its lines other than v
            Sz = [Ln for Ln in H.lines if Ln != v and all(in_Pi_z(p, al, be) for p in H.pts_on[Ln])]
            assert len(Sz) == q ** 3
            nrm = al * al + al * be + c * be * be if even else al * al + c * be * be
            Gz = (c0 * al + c1 * be) * nrm + be ** 3 if even else (c0 * al + c1 * be) * nrm - be ** 3
            Fz = Gz / nrm
            for Ln in Sz:
                pz = [p for p in H.pts_on[Ln] if in_Pi_z(p, 0, 0)]
                assert len(pz) == 1
                if nu(pz[0]) == Fz:
                    W.add(Ln)
    assert len(W) == q * q * (q * q - 1), len(W)
    # exactness: every free point (not in Pi, at distance 5 from v: not with x2 = x5 = 0) is on exactly one whisker
    cnt = {}
    for Ln in W:
        for p in H.pts_on[Ln]:
            cnt[p] = cnt.get(p, 0) + 1
    for p in H.points:
        if (not in_Pi_z(p, 0, 0)) and not (p[3] == 0 and p[6] == 0):
            assert cnt.get(p, 0) == 1, 'whisker set is not exact'
    Pv = set(H.pts_on[v])
    Lv = {Ln for p in Pv for Ln in H.lines_on[p]} - {v}
    RL = Lv | W
    assert len(RL) == q * (q ** 3 + 1)
    RH = {p for Ln in S for p in H.pts_on[Ln]}
    assert len(RH) == (q + 1) * (q ** 3 + 1)
    return RH, RL, S, v


def is_segment_set(H, R):
    """Definition 4.4: for every p in R the other points of R collinear with p all lie on one line through p."""
    R = set(R)
    return all(sum(1 for Ln in H.lines_on[p] if any(x in R and x != p for x in H.pts_on[Ln])) <= 1 for p in R)


def is_dual_segment_set(H, R):
    """The same with points and lines exchanged (a set of lines)."""
    R = set(R)
    return all(sum(1 for p in H.pts_on[Ln] if any(M in R and M != Ln for M in H.lines_on[p])) <= 1 for Ln in R)


# --------------------------------------------------------------------------------------------
# non-friendly transitions: a local duality sigma at a pairwise opposite point set
# --------------------------------------------------------------------------------------------

def pairwise_opposite_points(H, K):
    """The first K points, in the order of H.points, that are pairwise opposite (distance 6 in the incidence graph)."""
    G = H.graph()
    chosen, dist = [], []
    for p in H.points:
        if all(d.get(p) == 6 for d in dist):
            chosen.append(p)
            dist.append(G.shortest_path_lengths(p))
            if len(chosen) == K:
                return chosen
    raise ValueError('not enough pairwise opposite points')


def sigma_local_duality(H, Rp, Rs):
    r"""
    A bijection sigma: points -> lines of H(q) which is a local duality at every point of Rp (D7_HEXAGON.md Proposition 5.2 and
    Corollary 5.3(a); research/synthetic/conics2/typed_build.sigma_from_ovoid): sigma(Rp[i]) = Rs[i]; the q(q+1) points
    collinear with Rp[i] go onto the q(q+1) lines concurrent with Rs[i] (in the order of H.points / H.lines); all remaining
    points go onto the remaining lines in that order.   Rp: pairwise opposite points; Rs: pairwise opposite lines.
    """
    pidx = {p: i for i, p in enumerate(H.points)}
    lidx = {Ln: i for i, Ln in enumerate(H.lines)}
    sig, usedL = {}, set()
    for x, l in zip(Rp, Rs):
        near_pts = sorted({z for Ln in H.lines_on[x] for z in H.pts_on[Ln]} - {x}, key=pidx.get)       # collinear with x
        near_lns = sorted({M for z in H.pts_on[l] for M in H.lines_on[z]} - {l}, key=lidx.get)         # concurrent with l
        assert not any(z in sig for z in near_pts) and not (set(near_lns) & usedL) and x not in sig and l not in usedL
        sig[x] = l
        usedL.add(l)
        for z, M in zip(near_pts, near_lns):
            sig[z] = M
            usedL.add(M)
    restP = [p for p in H.points if p not in sig]
    restL = [Ln for Ln in H.lines if Ln not in usedL]
    assert len(restP) == len(restL)
    sig.update(zip(restP, restL))
    assert len(sig) == H.N and len(set(sig.values())) == H.N
    # sanity: local duality at every x in Rp
    for x in Rp:
        near_pts = {z for Ln in H.lines_on[x] for z in H.pts_on[Ln]} - {x}
        near_lns = {M for z in H.pts_on[sig[x]] for M in H.lines_on[z]} - {sig[x]}
        assert {sig[z] for z in near_pts} == near_lns
    return sig


# --------------------------------------------------------------------------------------------
# the typed level structure
# --------------------------------------------------------------------------------------------

def typed_transition_rule(H, types, RH, RL, sig, Rp):
    r"""
    The transitions of the typed layouts (D7_HEXAGON.md section 6; typed_build.py): returns a function (j, k) -> (img, freed)
    where img maps the elements of H(q) used as structure points of copy j to the elements used as structure lines of copy
    j+k, and freed is the set of sources whose incidence is deleted:
        H -> D  (friendly): img = identity,        freed = RH  (points of the Hermitian spread)
        D -> H  (friendly): img = identity,        freed = RL  (lines meeting v, plus whiskers)
        H -> H           : img = sigma,            freed = Rp  (pairwise opposite points, sigma a local duality there)
        D -> D           : img = sigma^-1,         freed = sigma(Rp)
    """
    L = len(types)
    ident_p = {p: p for p in H.points}
    ident_l = {Ln: Ln for Ln in H.lines}
    sinv = {M: p for p, M in sig.items()}
    sigRp = {sig[p] for p in Rp}

    def rule(j, k):
        a = types[j]
        b = types[(j + k) % L]
        if a == 'H' and b == 'D':
            return ident_p, RH
        if a == 'D' and b == 'H':
            return ident_l, RL
        if a == 'H' and b == 'H':
            return sig, set(Rp)
        return sinv, sigRp
    return rule


def build_d7(H, types, rule, hub_edges, n_line_hubs, n_point_hubs):
    r"""
    The level structure with freed sets and hubs, as a Sage Graph.
    H            a Hexagon (hexagon.sage)
    types        string over 'H','D' of odd length L = 2r+1
    rule(j, k)   -> (img, freed) for the transition from copy j to copy j+k (k = 1..r), see typed_transition_rule
    hub_edges    list of pairs (a, b): line-hub a joined to point-hub b
    n_line_hubs, n_point_hubs   numbers of hubs; hub h takes the h-th free slot of every copy
    """
    L = len(types)
    assert L % 2 == 1 and set(types) <= {'H', 'D'}
    r = (L - 1) // 2
    pidx = {p: i for i, p in enumerate(H.points)}
    lidx = {Ln: i for i, Ln in enumerate(H.lines)}
    idx = lambda e: pidx[e] if e[0] == 0 else lidx[e]

    def vertex(j, e):                                   # the vertex of copy j for the element e of H(q)
        s = (0 if e[0] == 0 else 1) if types[j] == 'H' else (1 if e[0] == 0 else 0)
        return (s, 'copy', j, e)

    G = Graph(multiedges=False, loops=False)
    # (1) the copies: all flags of H(q) in every copy
    for j in range(L):
        for Ln in H.lines:
            for p in H.pts_on[Ln]:
                G.add_edge(vertex(j, p), vertex(j, Ln))
    A_slots = [[] for _ in range(L)]                    # freed structure points of copy j (one slot per deleted incidence)
    B_slots = [[] for _ in range(L)]                    # freed structure lines of copy j
    for j in range(L):
        for k in range(1, r + 1):
            j2 = (j + k) % L
            img, freed = rule(j, k)
            # (2) the transition j -> j+k: the matching incidence x ~ img(x) between the copies, except at the freed elements
            for x, y in img.items():
                if x not in freed:
                    G.add_edge(vertex(j, x), vertex(j2, y))
            # (3) the slots left by the deleted incidences (sources in the order of their index in H)
            for x in sorted(freed, key=idx):
                A_slots[j].append(vertex(j, x))
                B_slots[j2].append(vertex(j2, img[x]))
    assert n_line_hubs <= min(len(s) for s in A_slots) and n_point_hubs <= min(len(s) for s in B_slots)
    # (4) line-hubs: line-hub h is incident with the h-th free slot (a structure point) of every copy
    for h in range(n_line_hubs):
        for j in range(L):
            G.add_edge((1, 'hub', h), A_slots[j][h])
    # (5) point-hubs: point-hub h is incident with the h-th free slot (a structure line) of every copy
    for h in range(n_point_hubs):
        for j in range(L):
            G.add_edge((0, 'hub', h), B_slots[j][h])
    # (6) the hub graph: line-hub a ~ point-hub b
    for a, b in hub_edges:
        G.add_edge((1, 'hub', a), (0, 'hub', b))
    return G


def cycle_hub_graph(K):
    """The 2K-cycle on K line-hubs and K point-hubs: line-hub i ~ point-hub i and point-hub i ~ line-hub i+1 (degree 2)."""
    return sorted({(i, i) for i in range(K)} | {((i + 1) % K, i) for i in range(K)})


def build_d7_typed(q, types, K, hub_edges=None):
    """H(q), pairwise opposite R' of size K, Rs = the first K spread lines other than v, sigma, the freed sets of the typed
    layout, and K line-hubs and K point-hubs joined by hub_edges (default: the 2K-cycle).  Returns (G, data)."""
    H = hexagon(q)
    if 'D' in types:                        # friendly transitions need the freed sets R_H, R_L (whiskers: q >= 3)
        RH, RL, S, v = friendly_sets(H)
    else:                                   # only H -> H transitions: the spread lines give the target lines of sigma
        RH = RL = None
        _, _, S = hermitian_spread(H)
        v = line_v(H)
    Rp = pairwise_opposite_points(H, K)
    Rs = [Ln for Ln in S if Ln != v][:K]
    sig = sigma_local_duality(H, Rp, Rs)
    rule = typed_transition_rule(H, types, RH, RL, sig, Rp)
    if hub_edges is None:
        hub_edges = cycle_hub_graph(K)
    G = build_d7(H, types, rule, hub_edges, K, K)
    return G, dict(H=H, RH=RH, RL=RL, S=S, v=v, Rp=Rp, Rs=Rs, sig=sig, rule=rule, hub_edges=hub_edges)


# --------------------------------------------------------------------------------------------
# check
# --------------------------------------------------------------------------------------------

def report(G, expect_n, expect_deg, expect_diam, bip=True, name=''):
    n = G.order()
    maxdeg = max(G.degree())
    isbip = G.is_bipartite()
    diam = G.diameter(algorithm='standard')
    ok = (n == expect_n and maxdeg == expect_deg and isbip == bip and diam == expect_diam)
    print(f'{name}: vertices {n} (expected {expect_n}), max degree {maxdeg} (expected {expect_deg}), '
          f'bipartite {isbip}, diameter {diam} (expected {expect_diam})  ->  {"OK" if ok else "MISMATCH"}', flush=True)
    return ok


def check(q, types='HDH', K=3):
    r"""Builds the typed level structure for H(q), the given type string and K hubs per side with the 2K-cycle as hub graph;
    expected: 2N L + 2K vertices, maximum degree Delta = q+1+r, bipartite, diameter 7.  The hub graph has degree <= q - r."""
    L = len(types)
    r = (L - 1) // 2
    G, data = build_d7_typed(q, types, K)
    H = data['H']
    # the combinatorial facts used: segment sets
    if data['RH'] is not None:
        assert is_segment_set(H, data['RH']) and is_dual_segment_set(H, data['RL'])
    return report(G, 2 * H.N * L + 2 * K, q + 1 + r, 7, name=f'q={q} types {types}, r={r}, {K}+{K} hubs on a {2 * K}-cycle')


def control_random_sigma(q=3, K=3):
    """Negative control: three copies of H(q), the same freed set R' on every transition, but the matching is a RANDOM
    bijection points -> lines instead of a local duality at R'.  Theorem 4.6 does not apply and the diameter is > 7."""
    import random
    H = hexagon(q)
    Rp = pairwise_opposite_points(H, K)
    lines = list(H.lines)
    random.Random(int(5)).shuffle(lines)
    bad = dict(zip(H.points, lines))
    rule = typed_transition_rule(H, 'HHH', None, None, bad, Rp)
    G = build_d7(H, 'HHH', rule, cycle_hub_graph(K), K, K)
    d = G.diameter(algorithm='standard')
    print(f'control (q={q}, HHH, random bijection instead of a local duality): {G.order()} vertices, diameter {d} (> 7 expected)  ->  '
          f'{"OK" if d > 7 else "UNEXPECTED"}', flush=True)
    return d > 7


if 'NO_AUTO_CHECK' not in globals():
    assert check(2, 'HHH', 1)          # smallest case: three copies of H(2), one line-hub and one point-hub (hub degree <= q - r = 1)
    assert check(3, 'HHH', 3)          # three copies of H(3), sigma on every transition (check_d7.py's assembly)
    assert check(3, 'HDH', 3)          # H -> D and D -> H friendly (spread points; lines meeting v + whiskers), H -> H by sigma
    assert check(3, 'HDHDH', 1)        # r = 2: five copies, hub degree <= q - r = 1, one hub on each side
    assert check(4, 'HDH', 3)          # q even (whisker formula of POLISHED.md Theorem 6.14), 8,196 vertices
    assert control_random_sigma(3, 3)
