"""Split each found graph's edges into PG incidences, edges at the extra vertices, and filler.

Filler = an edge between two old PG vertices that is not a PG incidence.  We check that the
graph without its filler still has diameter 3, and list the PG incidences that were removed.
"""
import json, sys
sys.path.insert(0, '/Users/dogaozden/AI_Projects/math/research/plus2')
from al import al_named
from diff_al import FILES, ROOT, norm
import lib

SPECIAL = {'Q0', 'M0', 'hp', 'hl', 'NEW0', 'NEW1'}


def pg_incident(a, b, F):
    """a a point name, b a line name, both PG elements: incidence in PG(2,q)."""
    if a[0] == 'pt':
        x, y = a[1], a[2]
        if b[0] == 'ln':
            return y == F.add(F.mul(b[1], x), b[2])
        if b[0] == 'L':
            return len(b) == 2 and b[1] == x
    if a[0] == 'P':
        if len(a) == 1:
            return b[0] == 'L'
        return (b[0] == 'ln' and b[1] == a[1]) or b == ('L',)
    return False


def analyse(q, n1, e1):
    n0, e0, names, F = al_named(q)
    names = dict(names)
    names[n0] = ('NEW0',)
    names[n0 + 1] = ('NEW1',)
    pts = {u for u, v in e0}
    pg, special, filler = [], [], []
    for u, v in norm(e1):
        a, b = (names[u], names[v]) if u in pts or names[u][0] == 'NEW0' else (names[v], names[u])
        if a[0] in SPECIAL or b[0] in SPECIAL:
            special.append((a, b))
        elif pg_incident(a, b, F):
            pg.append((a, b))
        else:
            filler.append((a, b))
    # PG incidences missing
    pg_all = []
    for p in [nm for nm in names.values() if nm[0] in ('pt', 'P')]:
        for l in [nm for nm in names.values() if nm[0] in ('ln', 'L')]:
            if pg_incident(p, l, F):
                pg_all.append((p, l))
    missing = sorted(set(pg_all) - set(pg))
    ids = {nm: i for i, nm in names.items()}
    core = [(ids[a], ids[b]) for a, b in pg + special]
    return pg, special, filler, missing, lib.bad_pairs(n1, core, 3)


if __name__ == '__main__':
    for q, f in FILES.items():
        n1, e1 = json.load(open(ROOT + f))['output']
        pg, special, filler, missing, bad = analyse(q, n1, e1)
        print(f'q={q}: PG incidences kept {len(pg)}, missing {len(missing)}: {missing}')
        print(f'   edges at extra vertices {len(special)}, filler {len(filler)}, '
              f'bad pairs without filler {bad}')
        for a, b in sorted(special):
            if not ((a[0] == 'hp' or a[0] == 'NEW0') and b[0] == 'ln') and not (b[0] in ('hl', 'NEW1') and a[0] == 'pt' and True):
                pass
        sp = {}
        for a, b in special:
            for x, y in ((a, b), (b, a)):
                if x[0] in SPECIAL:
                    sp.setdefault(x, []).append(y)
        for x in sorted(sp):
            ys = sp[x]
            short = [y for y in ys if not ((y[0] == 'ln' and x[0] in ('hp', 'NEW0')) or (y[0] == 'pt' and x[0] in ('hl', 'NEW1')))]
            rows = sorted({y[2] for y in ys if y[0] in ('ln', 'pt')})
            print('   ', x, 'deg', len(ys), 'rows of ln/pt nbrs', rows if len(rows) < 4 else f'{len(rows)} rows',
                  'other nbrs', sorted(set(short) - {y for y in ys if y[0] in ('ln','pt') and x[0] in ('Q0','M0')}) if True else '')
