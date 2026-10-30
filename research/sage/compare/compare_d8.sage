r"""
Compare d8_gomez_omegaH.sage with the lab's Python builder research/synthetic/checks/check_d8.py (function omega).

  (1) q = 2 ('ab') and q = 3 ('aba'), thesis labelling, reading 2, with the SAME pairing of point labels with line labels
      (the Python builder uses a random shuffle sigma; it is fed to the Sage builder): EXACT edge-set equality after
      relabelling the Python vertices by the Sage labels.
  (2) q = 3, the repaired structure: Python omega() on the audit base and the audit labelling (reading 1, inner = 'L'*15)
      against the Sage graph (the same labelling transported to the coordinates of H(3)): EXACT edge-set equality, and
      the Sage graph is isomorphic to the Python one (G.is_isomorphic) as a second statement.
Python vertex numbering: copy c, base vertex v (points 0..N-1, lines N..2N-1): c*2N + v;  new element (t, bar, k): 5 alpha 2N + 10t + 5bar + k.
Run from research/sage:  sage compare/compare_d8.sage
"""
import sys, os, random
HERE = os.path.abspath('.')
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
NO_AUTO_CHECK = True
load('d8_gomez_omegaH.sage')
CH = os.path.join(REPO, 'research', 'synthetic', 'checks')
sys.path.insert(0, CH)
import check_d8 as PY
import check_d6 as PY6


def sage_edges(G):
    return {frozenset(e[:2]) for e in G.edges(sort=False)}


def compare_thesis(q, types):
    alpha = len(types)
    # Python side: base hexagon, shuffle sigma as in check_d8.part2_3
    N, edges, pts, lines = PY.base_hexagon(q)
    rng = random.Random(int(10) + int(q))
    sigma = list(range(N)); rng.shuffle(sigma)
    inner = PY.readings(types)['reading 2']
    g, H0 = PY.omega(N, edges, types, inner, [list(range(N))] * (5 * alpha), [sigma] * (5 * alpha))
    # Sage side
    H = hexagon(q)
    pt_label = {tuple(int(x) for x in p[1:]): p for p in H.points}                 # coordinates (ints, q prime) -> label
    ln_label = {frozenset(tuple(int(x) for x in p[1:]) for p in H.pts_on[Ln]): Ln for Ln in H.lines}
    spt = [pt_label[tuple(p)] for p in pts]                                       # python point v -> label
    sln = [ln_label[frozenset(tuple(p) for p in L)] for L in lines]               # python line i  -> label
    P, L = thesis_labelling(H, types, pairing={spt[t]: sln[sigma[t]] for t in range(N)})
    G = build_d8_omega(H, types, reading(types, 2), P, L)

    def name(v):
        if v < H0:
            c, b = divmod(v, 2 * N)
            h = spt[b] if b < N else sln[b - N]
            return G_side_of(c, h), 'copy', c, h
        t, rest = divmod(v - H0, 10)
        bar, k = divmod(rest, 5)
        return (1 if bar == 0 else 0), 'class', bar, k, spt[t]

    def G_side_of(c, h):
        ps = 0 if sits_on_points(types, inner, c, 0) else 1
        return ps if h[0] == 0 else 1 - ps
    py_edges = {frozenset((name(u), name(v))) for u in range(g.n) for v in g.adj[u]}
    se = sage_edges(G)
    print(f'q={q} {types} thesis labelling: Python {len(py_edges)} edges, Sage {len(se)} edges; EXACT equal after relabelling: {py_edges == se}')
    return py_edges == se


def compare_repair():
    q, types = 3, 'aba'
    # Python side: audit base + labelling file
    with open(os.path.join(CH, 'omega_q3_base.txt')) as f:
        nb = int(f.readline())
        edges = [tuple(map(int, l.split())) for l in f if l.strip()]
    N = nb // 2
    vals = list(map(int, open(os.path.join(CH, 'omega_q3_aba_LLL_G13.lab')).read().split()))
    C = 15
    Pp = [vals[c * N:(c + 1) * N] for c in range(C)]
    Lp = [vals[C * N + c * N:C * N + (c + 1) * N] for c in range(C)]
    g, H0 = PY.omega(N, edges, types, 'L' * 15, Pp, Lp)
    # Sage side
    H = hexagon(q)
    P, L = read_base_and_labelling(H, os.path.join(CH, 'omega_q3_base.txt'), os.path.join(CH, 'omega_q3_aba_LLL_G13.lab'), types, C)
    G = build_d8_omega(H, types, reading(types, 1), P, L)
    # the transport phi (audit vertex number -> H(3) label) is recovered from the labels: label t of the thesis = point phi(t);
    # P[0] is the identity of the audit, so phi(t) = the key t of P[0] in file order  -> use canonical_label again
    Gb = Graph(edges)
    G1, m1 = H.graph().canonical_label(partition=[H.points, H.lines], certificate=True)
    G2, m2 = Gb.canonical_label(partition=[list(range(N)), list(range(N, 2 * N))], certificate=True)
    assert G1 == G2
    inv2 = {v: k for k, v in m2.items()}
    back = {inv2[m1[h]]: h for h in H.points + H.lines}
    inner = 'L' * 15

    def name(v):
        if v < H0:
            c, b = divmod(v, 2 * N)
            h = back[b] if b < N else back[b]            # audit lines are numbered N..2N-1 in the base file
            ps = 0 if sits_on_points(types, inner, c, 0) else 1
            return (ps if h[0] == 0 else 1 - ps), 'copy', c, h
        t, rest = divmod(v - H0, 10)
        bar, k = divmod(rest, 5)
        return (1 if bar == 0 else 0), 'class', bar, k, back[t]
    py_edges = {frozenset((name(u), name(v))) for u in range(g.n) for v in g.adj[u]}
    se = sage_edges(G)
    eq = py_edges == se
    print(f'q=3 repaired (audit labelling): Python {len(py_edges)} edges, Sage {len(se)} edges; EXACT equal after relabelling by the isomorphism audit base -> H(3): {eq}')
    return eq


ok = compare_thesis(2, 'ab')
ok &= compare_thesis(3, 'aba')
ok &= compare_repair()
print('compare_d8: ' + ('ALL EQUAL' if ok else 'DIFFERENCES'))
