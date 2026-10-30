r"""
Compare d6_theoremD_hexagon_doubling.sage with the repo's Python builders (research/synthetic/checks/check_d6.py for q = 2, 3 and
check_d6_even.py for q = 4, with incidence.py).  Run from research/sage/compare/:   sage compare_d6.sage
For each q:  (a) the Python hexagon and the Sage hexagon have the same flags after relabelling the points by their coordinates;
(b) the Hermitian spreads agree; (c) the exact whisker sets: if both use the same constants (c0, c1) they must agree; q = 2 is found by
a search in both programs, so the two sets may differ; (d) the doubled graphs: with the whisker set of the Python program fed to the Sage
builder the edge sets must be EXACTLY equal after relabelling; with the Sage program's own whisker set the graphs are compared with
is_isomorphic.
"""
import sys, os, itertools, runpy, io, contextlib
from pathlib import Path

HERE = Path(os.getcwd()).resolve()
REPO = HERE.parents[2]
CHECKS = REPO / 'research' / 'synthetic' / 'checks'
sys.path.insert(0, str(CHECKS))
sys.path.insert(0, str(REPO / 'research' / 'plus2' / 'coords'))
NO_AUTO_CHECK = True
load(str(HERE.parent / 'd6_theoremD_hexagon_doubling.sage'))
import check_d6 as PY6
from incidence import double_levels, Structure

results = []


def edge_set(G):
    return {frozenset(e) for e in G.edges(labels=False, sort=False)}


def compare_with(q, F, pt_map, Hpy, names, pi_lines, Spy, Wpy, Dpy, level_py, tag):
    """Hpy: python Structure of the hexagon; Dpy: python doubled Structure."""
    Hs = hexagon(q, F)
    # (a) hexagon flags
    line_of = {frozenset(Hs.pts_on[L]): L for L in Hs.lines}
    lmap = {n: line_of[frozenset(pt_map(p) for p in pi_lines[n])] for n in names}
    flags_py = {(pt_map(p), lmap[n]) for (p, n) in Hpy.flags}
    flags_sage = {(p, L) for L in Hs.lines for p in Hs.pts_on[L]}
    print(f'[{tag}] (a) hexagon flag sets equal after relabelling: {flags_py == flags_sage}')
    ok = flags_py == flags_sage
    # (b) spread
    conf0 = d6_configuration(Hs)
    Spy_s = {lmap[n] for n in Spy}
    print(f'[{tag}] (b) Hermitian spread equal: {Spy_s == set(conf0["spread"])}   (Sage c = {conf0["c"]})')
    ok &= Spy_s == set(conf0['spread'])
    # (c) whiskers
    Wpy_s = sorted(lmap[n] for n in Wpy)
    print(f'[{tag}] (c) whisker sets: Sage default {"=" if sorted(conf0["W"]) == Wpy_s else "!="} Python  '
          f'(|W| = {len(Wpy_s)})')
    # (d) doubled graphs
    GS = build_d6_theoremD(q, 2, H=Hs, whiskers=Wpy_s)
    edges_py = set()
    for (a, b) in Dpy.flags:
        pa, wa = a
        nb, wb = b
        edges_py.add(frozenset(((0,) + pt_map(pa)[1:] + (tuple(wa),), lmap[nb] + (tuple(wb),))))
    eq = edges_py == edge_set(GS)
    print(f'[{tag}] (d) Sage doubling with the Python whiskers: {GS.order()} vertices; edge set EXACTLY equal to the Python one: {eq}')
    ok &= eq
    if sorted(conf0['W']) != Wpy_s:
        GD = build_d6_theoremD(q, 2, H=Hs, conf=conf0)
        iso = GD.is_isomorphic(GS)
        print(f'[{tag}]     Sage default whiskers: graph has {GD.order()} vertices, degrees {sorted(set(GD.degree()))}; '
              f'is_isomorphic to the Python graph: {iso}')
    results.append((tag, ok))
    return ok


# ---- q = 2, 3: check_d6.py
for q, pi, wmode, params in ((3, lambda p: (p[0] + 1 * p[4]) % 3 == 0, ('formula', 1, 1, 2), (1, 2)),
                             (2, lambda p: (p[3] + p[0] + p[4]) % 2 == 0, ('search',), None)):
    Hpy, names, lines = PY6.hexagon(q)
    pi_lines = {n: lines[i] for i, n in enumerate(names)}
    v = next(L for i, L in enumerate(names) if all(p[k] == 0 for p in lines[i] for k in (0, 2, 3, 4, 5)))
    Spts = {p for p in Hpy.points if pi(p)}
    S = [L for L in Hpy.lines if Hpy.pts_on[L] <= Spts]
    dv = Hpy.distances_from(v)
    Pv = Hpy.pts_on[v]
    Lv = [L for L in Hpy.lines if L != v and Hpy.pts_on[L] & Pv]
    free = [p for p in Hpy.points if p not in Spts and dv[p] == 5]
    cand = [L for L in Hpy.lines if dv[L] == 6 and L not in set(S)]
    if wmode[0] == 'formula':
        W = PY6.whiskers_formula(Hpy, lines, names, q, *wmode[1:])
    else:
        sol = PY6.exact_cover(set(free), {L: frozenset(Hpy.pts_on[L] & set(free)) for L in cand})
        W = set(sol)
    level = {}
    for x in [*S, *Spts, *Lv, *W]:
        level[x] = 0
    for x in [*S, *Pv]:
        level[x] = 1
    level[v] = 2
    Dpy = double_levels(Hpy, level, 2)
    F = GF(q)
    compare_with(q, F, lambda p: (0,) + tuple(F(x) for x in p), Hpy, names, pi_lines, S, W, Dpy, level, f'q={q}')

# ---- q = 4: check_d6_even.py is a script; run it and take its variables
buf = io.StringIO()
ns = {}
try:
    with contextlib.redirect_stdout(buf):
        ns = {'__name__': 'py_even', '__file__': str(CHECKS / 'check_d6_even.py')}
        exec(compile(open(CHECKS / 'check_d6_even.py').read(), 'check_d6_even.py', 'exec'), ns)
except SystemExit:
    pass
print('check_d6_even.py output:', buf.getvalue().strip().replace('\n', ' | '))

F4 = GF(4, 't')
pi_lines4 = {n: ns['lines'][i] for i, n in enumerate(ns['names'])}
compare_with(4, F4, lambda p: (0,) + tuple(F4.from_integer(int(x)) for x in p), ns['H'], ns['names'], pi_lines4,
             ns['S'], ns['W'], ns['D'], ns['level'], 'q=4')
print('ALL COMPARISONS EQUAL' if all(ok for _, ok in results) else 'DIFFERENCES FOUND', results)
