r"""
Compare the Sage graphs of d3_four_hats.sage and d3_16_three_gadgets.sage with the lab's Python builders.

  (1) four hats: for several q and every admissible (a, c) tried, the Sage graph (core and with filler)
      against research/plus2/coords/coords.py, EXACT edge-set equality after relabelling.  The Sage field is
      built with the same modulus as coords.py's GF(q), and the elements are matched by their base-p digits.
  (2) the (16,3) record: the Sage graph against research/d3d6/graphs/sym3_q13_d16_n396.json (the file
      that was verified as a record), EXACT edge-set equality after relabelling.

Run from research/sage:  sage compare/compare_d3.sage
"""
import sys, json, os
HERE = os.path.dirname(os.path.abspath('.')) if False else os.path.abspath('.')
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
NO_AUTO_CHECK = True
load('d3_four_hats.sage')
sys.path.insert(0, os.path.join(REPO, 'research', 'plus2', 'coords'))
import coords as PY


def sage_field_like(pyF):
    """GF(q) in Sage with the same modulus as coords.GF, plus the map integer -> element."""
    q = pyF.q
    if pyF.k == 1:
        F = GF(q)
        return F, (lambda x: F(x))
    R = PolynomialRing(GF(pyF.p), 'x')
    xx = R.gen()
    f = xx ** pyF.k + sum(pyF.mod[i] * xx ** i for i in range(pyF.k))
    F = GF(q, 't', modulus=f)
    t = F.gen()
    return F, (lambda x: sum(((x // pyF.p ** i) % pyF.p) * t ** i for i in range(pyF.k)))


def relabel(F, conv, name):
    """Python vertex name -> Sage label of d3_four_hats.sage."""
    if name[0] == 'pt':
        return (0,) + tuple(conv(x) for x in name[1])
    if name[0] == 'ln':
        return (1,) + tuple(conv(x) for x in name[1])
    if name[0] == 'Q':
        return (0, 'Q')
    if name[0] == 'M':
        return (1, 'M')
    if name[0] == 'H':
        return (0, 'H', conv(name[1]))
    if name[0] == 'K':
        return (1, 'K', conv(name[1]))
    raise ValueError(name)


def compare_four_hats(q, choices):
    ok = True
    for a, c in choices:
        fr = PY.Frame(q, a, c)
        F, conv = sage_field_like(fr.F)
        core = PY.build_all(fr)
        for filler in (False, True):
            inc = PY.filler(fr, core, q + 2) if filler else core
            E_py = {frozenset((relabel(F, conv, p), relabel(F, conv, L))) for p, L in inc}
            G = build_d3_four_hats(q, a=conv(a), c=conv(c), filler=filler, F=F)
            E_sg = {frozenset(e[:2]) for e in G.edges(sort=False)}
            same = (E_py == E_sg) and G.order() == len(set(relabel(F, conv, v) for v in fr.points + fr.new_points + fr.lines + fr.new_lines))
            print(f'  four hats q={q} a={a} c={c} filler={filler}: edges {len(E_sg)} vs {len(E_py)}, '
                  f'exact edge-set equality: {same}')
            ok &= same
    return ok


def compare_three_hats(q, a_list):
    ok = True
    for a in a_list:
        fr = PY.Frame(q, a, None)
        F, conv = sage_field_like(fr.F)
        core = PY.build_all(fr)
        E_py = {frozenset((relabel(F, conv, p), relabel(F, conv, L))) for p, L in core}
        G = build_d3_three_hats(q, a=conv(a), F=F)
        E_sg = {frozenset(e[:2]) for e in G.edges(sort=False)}
        print(f'  three hats q={q} a={a}: edges {len(E_sg)} vs {len(E_py)}, exact edge-set equality: {E_py == E_sg}')
        ok &= (E_py == E_sg)
    return ok


def compare_16_3():
    load('d3_16_three_gadgets.sage')
    sys.path.insert(0, os.path.join(REPO, 'research', 'd3d6'))
    sys.path.insert(0, os.path.join(REPO, 'research', 'plus2'))
    sys.path.insert(0, os.path.join(REPO, 'problems', 'bipartite_dd'))
    from singer import singer_plane as py_singer
    from multi_gadget import gadget_incidences, to_graph
    pts, lines = py_singer(13)
    frames = [tuple(f) for f in json.load(open(os.path.join(REPO, 'research', 'd3d6', 'graphs', 'sym3_q13_frames.json')))]
    # the frames in the file are the frames used by d3_16_three_gadgets.sage
    mine = [(A, ell, X) for (A, ell, X) in frames_16_3()]
    assert [(f[0], f[1], list(f[3])) for f in frames] == mine
    inc = gadget_incidences(lines, frames)
    names = sorted({a for a, b in inc}, key=str) + sorted({b for a, b in inc}, key=str)     # the id order of to_graph
    J = json.load(open(os.path.join(REPO, 'research', 'd3d6', 'graphs', 'sym3_q13_d16_n396.json')))['output']
    assert J[0] == len(names) == 396
    plane = singer_plane(13)
    sym = {0: 0, 1: 1, '0': 0, '1': 1, 'a': 'a', 'c': 'c'}

    def lab(nm):
        if nm[0] == 'p': return plane['pt'][nm[1]]
        if nm[0] == 'l': return plane['ln'][nm[1]]
        if nm[0] == 'Q': return (0, 'Q', nm[1])
        if nm[0] == 'M': return (1, 'M', nm[1])
        if nm[0] == 'H': return (0, 'H', nm[1], sym[nm[2]])
        if nm[0] == 'K': return (1, 'K', nm[1], sym[nm[2]])
    E_json = {frozenset((lab(names[u]), lab(names[v]))) for u, v in J[1]}
    G = build_d3_16_three_gadgets()
    E_sg = {frozenset(e[:2]) for e in G.edges(sort=False)}
    same = E_json == E_sg
    print(f'  (16,3): Sage {G.order()} vertices {len(E_sg)} edges, json {J[0]} vertices {len(E_json)} edges, '
          f'exact edge-set equality with sym3_q13_d16_n396.json: {same}')
    return same


ok = True
print('four hats vs coords.py')
ok &= compare_four_hats(4, [(2, 3), (3, 2)])
ok &= compare_four_hats(5, [(a, c) for a in range(2, 5) for c in range(2, 5) if a != c])
ok &= compare_four_hats(7, [(2, 3), (5, 4)])
ok &= compare_four_hats(8, [(2, 3), (7, 5)])
ok &= compare_four_hats(9, [(2, 3), (8, 4)])
print('three hats (Araujo-Pardo--Lopez) vs coords.py')
ok &= compare_three_hats(4, [2, 3])
ok &= compare_three_hats(5, [2, 3, 4])
ok &= compare_three_hats(9, [2, 5])
print('(16,3) vs the verified record file')
ok &= compare_16_3()
print('ALL COMPARISONS PASS' if ok else 'SOME COMPARISON FAILED')
