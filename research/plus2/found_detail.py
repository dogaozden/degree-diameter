"""Per found graph: off-row neighbours of the extra vertices, and a minimal set of filler edges
that the diameter really needs (greedy: drop filler edges one at a time while diameter stays 3)."""
import json, sys
sys.path.insert(0, '/Users/dogaozden/AI_Projects/math/research/plus2')
from al import al_named
from diff_al import FILES, ROOT, norm
from found_core import analyse, SPECIAL
import lib

for q, f in FILES.items():
    n1, e1 = json.load(open(ROOT + f))['output']
    n0, e0, names, F = al_named(q)
    names = dict(names); names[n0] = ('NEW0',); names[n0 + 1] = ('NEW1',)
    ids = {nm: i for i, nm in names.items()}
    pg, special, filler, missing, bad = analyse(q, n1, e1)
    print(f'=== q={q}')
    for x in sorted({s for e in special for s in e if s[0] in SPECIAL}):
        nb = [b if a == x else a for a, b in special if x in (a, b)]
        if x[0] in ('Q0', 'M0'):
            main = [y for y in nb if y[0] in ('pt', 'ln') and y[1] == 0]
            print('  ', x, 'on row-0 vertical/horizontal elements with y in', sorted(y[2] for y in main),
                  '+', sorted(set(nb) - set(main)))
            continue
        rows = {}
        for y in nb:
            if y[0] in ('pt', 'ln'):
                rows.setdefault(y[2], []).append(y)
        mainrow = max(rows, key=lambda r: len(rows[r]))
        print('  ', x, f'full row y={mainrow}', '+', sorted(set(nb) - set(rows[mainrow])))
    core = [(ids[a], ids[b]) for a, b in pg + special]
    fill = [(ids[a], ids[b]) for a, b in filler]
    keep = list(fill)
    for e in fill:
        trial = [x for x in keep if x != e]
        if lib.bad_pairs(n1, core + trial, 3) == 0:
            keep = trial
    print('   needed filler edges (greedy):', [(names[u], names[v]) for u, v in keep])
