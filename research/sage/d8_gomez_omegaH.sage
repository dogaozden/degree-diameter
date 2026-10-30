r"""
Diameter 8: Gomez's compound graphs Omega H_q on copies of the split Cayley hexagon H(q), with a labelling
for every copy (SYNTHETIC.md section 6; research/theorems/OMEGA_NOTE.md; reference check
research/synthetic/checks/check_d8.py).   SMALL q ONLY: q = 2, 3 (the table cells are q = 7,...,13 with 10^6-10^7 vertices).

Run (from the directory research/sage/):   sage d8_gomez_omegaH.sage
Needs hexagon.sage (same directory) and data/omega_q3_base.txt, data/omega_q3_aba_LLL_G13.lab (copies of the files in
research/synthetic/checks/).

WHAT THIS FILE SHOWS (honestly): the construction exactly as defined by Gomez (one labelling, the same in every copy)
has diameter >= 9 for every q (SYNTHETIC.md Theorem 6.2); the claim "diameter 8" fails.  Giving each copy its own
labelling repairs it at q = 2, 3 (search results), not for geometric labellings at q >= 7.  check(q) builds both and
prints what each gives.

Notation (SYNTHETIC.md 6.1).  alpha = floor((q+3)/2) blocks of five copies; copy c = 5B + i, block B with type 'a'
or 'b' (string `types`), position i in Z_5.  Ten classes: unbarred k and barred kbar, k in Z_5.  Class k (bar = 0) or
kbar (bar = 1) meets in a block of type a:   bar 0: positions k-1, k+1;  bar 1: positions k+2, k+3
                                 in a block of type b:   bar 0: positions k+3, k+4;  bar 1: positions k-1, k+1.
A class has one new element for each LABEL t (the labels are the N points of H(q), used as names).  In a copy c that the
class meets, the new element with label t is incident with exactly one element of that copy: the point P_c(t) or the
line L_c(t); P_c, L_c are bijections from the labels to the points, resp. the lines, of H(q) (the labelling of copy c).
Which of the two is given by `inner`: inner[c] = 'P' or 'L' says whether the INNER class of copy c (a-block: the
unbarred classes; b-block: the barred classes) sits on points or on lines; the other bar sits on the other kind.
 reading 2 (SYNTHETIC.md 6.1):  inner = 'P' in a-blocks, 'L' in b-blocks  (unbarred classes on points, barred on lines);
 reading 1 with all inner classes on lines: inner = 'L' in every copy (a b-copy is then a copy of the dual hexagon).

Vertex labels (first entry = side of the bipartition, 0/1):
    (s, 'copy', c, h)          the element h of the copy c; h is a label of H(q) from hexagon.sage:
                               h = (0, x0..x6) a point of H(q), h = (1, ...) a line of H(q).  In the copy c the points of H(q)
                               are on side 0 if the unbarred classes sit on points in c ("normal" copy), else on side 1.
    (s, 'class', bar, k, t)    the new element of class k (bar = 0: unbarred) or kbar (bar = 1: barred) with label t;
                               t is the point of H(q) used as the name of the label (in the thesis labelling t = P_c(t)).
                               Unbarred classes are on side 1, barred classes on side 0 (so in reading 2 an unbarred
                               class is a new LINE through copies of a point, a barred class a new POINT on copies of a line).
"""
import itertools
import os

# ---- load the hexagon helper (no self-test), from the directory of this file or the current directory
_had_flag = 'NO_AUTO_CHECK' in globals()
NO_AUTO_CHECK = True
_here = os.path.dirname(os.path.abspath(globals().get('__file__', 'd8_gomez_omegaH.sage')))
for _p in (os.path.join(_here, 'hexagon.sage'), 'hexagon.sage'):
    if os.path.exists(_p):
        load(_p)
        break
else:
    raise IOError('hexagon.sage not found: run from research/sage/')
DATA_DIR = os.path.join(_here, 'data') if os.path.isdir(os.path.join(_here, 'data')) else 'data'
if not _had_flag:
    del NO_AUTO_CHECK


# --------------------------------------------------------------------------------------------
# Gomez's wiring: which classes meet which copies
# --------------------------------------------------------------------------------------------

def classes_meeting(types, c):
    """The classes (bar, k) that meet copy c = 5B + i (SYNTHETIC.md 6.1): in a block of type a the unbarred classes
    i-1, i+1 and the barred classes i+2, i+3; in a block of type b the unbarred classes i+1, i+2 and the barred i-1, i+1."""
    B, i = divmod(c, 5)
    if types[B] == 'a':
        return [(0, (i - 1) % 5), (0, (i + 1) % 5), (1, (i + 2) % 5), (1, (i + 3) % 5)]
    return [(0, (i + 1) % 5), (0, (i + 2) % 5), (1, (i - 1) % 5), (1, (i + 1) % 5)]


def sits_on_points(types, inner, c, bar):
    """True if the classes of the given bar sit on the POINTS of copy c (False: on the lines)."""
    on_inner = (bar == 0) == (types[c // 5] == 'a')       # a-block: unbarred is the inner bar; b-block: barred is
    return (inner[c] == 'P') == on_inner


def reading(types, which):
    """The string `inner` for reading 2 (unbarred on points, barred on lines) or reading 1 (all inner classes on lines)."""
    if which == 2:
        return ''.join(('P' if ty == 'a' else 'L') * 5 for ty in types)
    return 'L' * (5 * len(types))


# --------------------------------------------------------------------------------------------
# labellings
# --------------------------------------------------------------------------------------------

def thesis_labelling(H, types, pairing=None):
    """The labelling of the thesis: the same in every copy.  P_c(t) = t (the labels are the points of H(q)); L_c(t) =
    pairing[t], a fixed bijection from the points to the lines (the thesis leaves the pairing open; default: the i-th
    point with the i-th line in the order of H.points, H.lines).  Returns (P, L), lists of dicts indexed by the copy."""
    if pairing is None:
        pairing = dict(zip(H.points, H.lines))
    C = 5 * len(types)
    return [{t: t for t in H.points} for _ in range(C)], [dict(pairing) for _ in range(C)]


def read_base_and_labelling(H, base_file, lab_file, types, ncopies):
    r"""The q = 3 repair (SYNTHETIC.md 6.3, OMEGA_NOTE.md C7): the labelling file of the lab's table audit is written on the
    audit's own base hexagon (an incidence graph on 2N numbered vertices, points 0..N-1, lines N..2N-1).  We find the
    isomorphism phi of that graph (points -> points, lines -> lines) onto H(3) of hexagon.sage and transport the labelling:
    P_c(t) = phi(P_c[t]), L_c(t) = phi(N + L_c[t]), the label t being named by the point phi(t).
    Returns (P, L) as in thesis_labelling.  The file holds 2*ncopies*N integers: P_0..P_{C-1}, then L_0..L_{C-1}."""
    N = H.N
    with open(base_file) as f:
        nb = int(f.readline())
        edges = [tuple(map(int, l.split())) for l in f if l.strip()]
    assert nb == 2 * N
    Gb = Graph(edges, multiedges=False, loops=False)
    vals = list(map(int, open(lab_file).read().split()))
    assert len(vals) == 2 * ncopies * N
    # type-preserving isomorphism by canonical forms with the partition (points | lines)
    for first, second in ((H.points, H.lines),):
        G1, m1 = H.graph().canonical_label(partition=[first, second], certificate=True)
        G2, m2 = Gb.canonical_label(partition=[list(range(N)), list(range(N, 2 * N))], certificate=True)
        if G1 == G2:
            break
    else:
        raise ValueError('the audit base is not isomorphic to H(3) preserving the two sides')
    inv2 = {v: k for k, v in m2.items()}
    back = {inv2[m1[h]]: h for h in H.points + H.lines}                  # audit vertex number -> label of H(3)
    # `first` = H.points means audit points = points of H(3); the swapped case would mean a dual embedding
    assert all(back[i][0] == 0 for i in range(N)) and all(back[N + i][0] == 1 for i in range(N)), \
        'the audit base is the dual of H(3): not supported'
    P = [{back[t]: back[vals[c * N + t]] for t in range(N)} for c in range(ncopies)]
    L = [{back[t]: back[N + vals[ncopies * N + c * N + t]] for t in range(N)} for c in range(ncopies)]
    return P, L


# --------------------------------------------------------------------------------------------
# the construction
# --------------------------------------------------------------------------------------------

def build_d8_omega(H, types, inner, P, L):
    r"""
    The incidence graph of Gomez's structure Omega H on the hexagon H = H(q) (a Hexagon of hexagon.sage).
    types   string over 'a','b' of length alpha (block types);   inner  string of length 5*alpha ('P'/'L', see above)
    P, L    labellings: P[c][t] a point and L[c][t] a line of H for every copy c and label t (t a point of H).
    """
    alpha = len(types)
    C = 5 * alpha
    assert len(inner) == C and len(P) == len(L) == C
    G = Graph(multiedges=False, loops=False)
    side_class = {0: 1, 1: 0}                                    # unbarred classes: side 1, barred classes: side 0

    def copy_vertex(c, h):
        ps = 0 if sits_on_points(types, inner, c, 0) else 1      # side of the points of H in copy c
        return ((ps if h[0] == 0 else 1 - ps), 'copy', c, h)

    for c in range(C):
        # (1) copy c of H(q): all flags of H(q)
        for Ln in H.lines:
            for p in H.pts_on[Ln]:
                G.add_edge(copy_vertex(c, p), copy_vertex(c, Ln))
        # (2) the new elements that meet copy c: for each of the four classes (bar, k) that meet c and each label t, the
        #     new element (bar, k, t) is joined to the point P_c(t) or to the line L_c(t) (never to both)
        for bar, k in classes_meeting(types, c):
            on_pts = sits_on_points(types, inner, c, bar)
            for t in H.points:
                x = P[c][t] if on_pts else L[c][t]
                G.add_edge((side_class[bar], 'class', bar, k, t), copy_vertex(c, x))
    return G


# --------------------------------------------------------------------------------------------
# check
# --------------------------------------------------------------------------------------------

def report(G, expect_n, expect_deg, expect_diam, bip=True, name='', at_least=False):
    n = G.order()
    maxdeg = max(G.degree())
    isbip = G.is_bipartite()
    diam = G.diameter(algorithm='standard') if hasattr(G, 'diameter') else None
    okd = (diam >= expect_diam) if at_least else (diam == expect_diam)
    ok = (n == expect_n and maxdeg == expect_deg and isbip == bip and okd)
    print(f'{name}: vertices {n} (expected {expect_n}), max degree {maxdeg} (expected {expect_deg}), '
          f'bipartite {isbip}, diameter {diam} (expected {">= " if at_least else ""}{expect_diam})  ->  '
          f'{"OK" if ok else "MISMATCH"}', flush=True)
    return ok


def check(q):
    r"""q = 2: types 'ab';  q = 3: types 'aba'.  Builds
      (i)  the thesis structure (one labelling, reading 2):  expected diameter 9 (Theorem 6.2: >= 9; computed 9),
      (ii) q = 3 only: the repaired structure with the audit labelling (reading 1, all inner classes on lines): diameter 8.
    Counts: 5(alpha+1)*2N vertices, maximum degree max(q+3, 2 alpha)."""
    assert q in (2, 3), 'only q = 2, 3 are feasible here (N = 63, 364)'
    alpha = (q + 3) // 2
    types = {2: 'ab', 3: 'aba'}[q]
    H = hexagon(q)
    n_expected = 5 * (alpha + 1) * 2 * H.N
    maxdeg = max(q + 3, 2 * alpha)
    ok = True
    P, L = thesis_labelling(H, types)
    G = build_d8_omega(H, types, reading(types, 2), P, L)
    ok &= report(G, n_expected, maxdeg, 9, name=f'q={q} {types}, thesis labelling, reading 2 (as defined: diameter >= 9)')
    if q == 3:
        P, L = read_base_and_labelling(H, os.path.join(DATA_DIR, 'omega_q3_base.txt'),
                                       os.path.join(DATA_DIR, 'omega_q3_aba_LLL_G13.lab'), types, 5 * alpha)
        G = build_d8_omega(H, types, reading(types, 1), P, L)
        ok &= report(G, n_expected, maxdeg, 8, name='q=3 aba, audit labelling (per-copy), reading 1 (repair)')
    return ok


if 'NO_AUTO_CHECK' not in globals():
    for q_ in (2, 3):
        check(q_)
