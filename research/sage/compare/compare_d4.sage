r"""
Compare the diameter-4 Sage graphs with the lab's Python builders (EXACT edge-set equality after relabelling).

  (1) Theorem A: d4_theoremA_ASq.sage against research/gq4x/as_w2.py (q = 3, 5, 7; prime q so that the integer
      field elements of the Python code are the elements of GF(q)).
  (2) Proposition C: d4_propC_Wq.sage against research/synthetic/checks/check_d4.py (`cyclic_W3`, `clones_shadows`
      and the explicit completion), q = 3, 5.  The completion depends on a numbering of the spread lines; the Sage
      function takes that numbering as an argument, and here it is taken from the Python code.
  (3) the (7,4) example: d4_7_4_359_Q45.sage against check_d4.py's `example_359` construction.

Run from research/sage:  sage compare/compare_d4.sage
"""
import sys, os, json
REPO = os.path.abspath(os.path.join(os.path.abspath('.'), '..', '..'))
NO_AUTO_CHECK = True
for p_ in ('research/gq4x', 'research/synthetic/checks', 'research/gq4', 'problems/bipartite_dd'):
    sys.path.insert(0, os.path.join(REPO, p_))


def edge_set(G):
    return {frozenset(e[:2]) for e in G.edges(sort=False)}


def compare_theoremA(q):
    load('d4_theoremA_ASq.sage')
    from as_gq import build
    from as_w2 import weighted_2ovoid
    F, pts, lines = build(q)
    W, eps, c2 = weighted_2ovoid(F, pts, 1)
    S = GF(q)
    G = build_d4_ASq(q, S)
    G0, points, mylines, onl = build_AS(q, S)
    by_set = {frozenset(onl[L]): L for L in mylines}                        # point set -> my line label
    plabel = lambda i: (0,) + tuple(S(x) for x in pts[i])
    E = set()
    for L in lines:
        lab = by_set[frozenset(plabel(i) for i in L)]
        for i in L:
            E.add(frozenset((plabel(i), lab)))
    for i, w in sorted(W.items()):                                          # clones in the order of as_w2.py
        for k in range(1, w + 1):
            cl = (0, 'clone') + plabel(i)[1:] + (k,)
            for L in lines:
                if i in L:
                    E.add(frozenset((cl, by_set[frozenset(plabel(j) for j in L)])))
    mine = edge_set(G)
    print(f'  Theorem A q={q}: Sage {G.order()} vertices {len(mine)} edges, Python {len(E)} edges, '
          f'exact edge-set equality: {E == mine}')
    return E == mine


def compare_propC(q):
    load('d4_propC_Wq.sage')
    import check_d4 as C
    Wp, O, spread = C.cyclic_W3(q)
    Wm = cyclic_W(q)
    by_set = {S_: L for L, S_ in Wm['lines'].items()}
    lab_line = lambda name: by_set[frozenset(Wp.pts_on[name])]
    assert set(O) == Wm['O'] and {frozenset(Wp.pts_on[L]) for L in spread} == {Wm['lines'][L] for L in Wm['spread']}
    w = {x: 1 for x in O}
    M = [L for L in spread for _ in range(2)]
    T = C.clones_shadows(Wp, w, M)
    clones = [x for x in T.points if isinstance(x, tuple) and x[1] == 'c']
    shadows = [L for L in T.lines if L[0] == 'sh']
    b = len(shadows)
    extra = {(c, shadows[(2 * i + k) % b]) for i, c in enumerate(clones) for k in (0, 1)}
    flags = T.flags | extra
    # relabel
    def lab_p(x):
        return Wm['pts'][x] if not isinstance(x, tuple) else (0, 'clone', Wm['pts'][x[0]])
    def lab_l(L):
        if L[0] == 'sh':
            idx = L[1]
            return (1, 'shadow', lab_line(spread[idx // 2]), idx % 2)
        return lab_line(L)
    E = {frozenset((lab_p(p), lab_l(L))) for p, L in flags}
    order = [lab_line(L) for L in spread]
    G = build_d4_propC(q, Wm, spread_order=order)
    mine = edge_set(G)
    print(f'  Proposition C q={q}: Sage {G.order()} vertices {len(mine)} edges, Python {len(E)} edges, '
          f'exact edge-set equality: {E == mine}')
    return E == mine


def compare_359():
    load('d4_7_4_359_Q45.sage')
    from gq_clones import q4
    import check_d4 as C
    q = 5
    pts, lines, ovoid = q4(q)
    data = json.load(open(os.path.join(REPO, 'research/synthetic/checks/q4_359_lines.json')))
    idx = {tuple(p): i for i, p in enumerate(pts)}
    O = set(ovoid)
    S = C.Structure(list(range(len(pts))), [('Q', j) for j in range(len(lines))],
                    {(x, ('Q', j)) for j, L in enumerate(lines) for x in L})
    lid = {frozenset(L): ('Q', j) for j, L in enumerate(lines)}
    M, standin = [], {}
    for mu, e in enumerate(data):
        L = lid[frozenset(idx[tuple(p)] for p in e['line'])]
        M.append(L)
        cl = {idx[tuple(p)] for p in e['clone_standins']}
        for x in S.pts_on[L]:
            standin[(mu, x)] = (x, 'c', 1) if x in cl else x
    T = C.clones_shadows(S, {x: 1 for x in O}, M, standin)
    F = GF(5)
    spts, slines, onl, sovoid = quadric_Q45(5)
    by_set = {frozenset(onl[L]): L for L in slines}
    pt_lab = lambda i: (0,) + tuple(F(x) for x in pts[i])
    def lab_p(x):
        return pt_lab(x) if not isinstance(x, tuple) else (0, 'clone', pt_lab(x[0]))
    def lab_l(L):
        if L[0] == 'sh':
            mu = L[1]
            return (1, 'shadow', mu, by_set[frozenset(tuple(F(y) for y in pts[i]) for i in S.pts_on[M[mu]])])
        return by_set[frozenset(tuple(F(y) for y in pts[i]) for i in S.pts_on[L])]
    E = {frozenset((lab_p(p), lab_l(L))) for p, L in T.flags}
    G = build_d4_7_4_359()
    mine = edge_set(G)
    print(f'  (7,4): Sage {G.order()} vertices {len(mine)} edges, Python {len(E)} edges, exact edge-set equality: {E == mine}')
    return E == mine


ok = True
print('Theorem A vs research/gq4x/as_w2.py')
for q_ in (3, 5, 7):
    ok &= compare_theoremA(q_)
print('Proposition C vs research/synthetic/checks/check_d4.py')
for q_ in (3, 5):
    ok &= compare_propC(q_)
print('(7,4) example vs research/synthetic/checks/check_d4.py')
ok &= compare_359()
print('ALL COMPARISONS PASS' if ok else 'SOME COMPARISON FAILED')
