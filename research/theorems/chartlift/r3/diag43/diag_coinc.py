"""Complete the (4,3) both-diagonal classification: labelled point configurations WITH coincidences (w_s = w_t).
Up to PGL(4,3) a labelled 4-tuple of points is a set partition of {0,1,2,3} (which labels share a point) plus the
orbit of the distinct points: 3 distinct points are independent or collinear (one orbit each), 2 or 1 distinct points
form one orbit.  Runs the joint search of diag_exhaust3.py on every pair (w-config, b-config) in which at least one side
has a coincidence (the 49 coincidence-free pairs are in diag_charts_all.out)."""
import importlib.util, sys, itertools
spec = importlib.util.spec_from_file_location('de', 'diag_exhaust3.py'); de = importlib.util.module_from_spec(spec)
sys.argv = ['x']; spec.loader.exec_module(de)
e = [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]
def partitions(s):
    if not s: yield []; return
    first, rest = s[0], s[1:]
    for p in partitions(rest):
        for i in range(len(p)): yield p[:i] + [[first] + p[i]] + p[i + 1:]
        yield [[first]] + p
CO = {}
for p in partitions([0, 1, 2, 3]):
    r = len(p)
    if r == 4: continue
    geoms = {3: [('ind', [e[0], e[1], e[2]]), ('col', [e[0], e[1], (1, 1, 0, 0)])], 2: [('two', [e[0], e[1]])], 1: [('one', [e[0]])]}[r]
    for gname, pts in geoms:
        W = [None] * 4
        for bi, block in enumerate(sorted(p)):
            for lab in block: W[lab] = pts[bi]
        CO['co' + '|'.join(''.join(map(str, b)) for b in sorted(p)) + '_' + gname] = W
ALL = dict(de.REPS); ALL.update(CO)
print(len(CO), 'coincidence configurations;', len(ALL), 'in all', flush=True)
found = 0; n = 0
for wn, W in ALL.items():
    for bn, B in ALL.items():
        if wn in de.REPS and bn in de.REPS: continue
        sizes, out = de.search(W, B); n += 1
        if out.startswith('FOUND'): found += 1; print('COVERABLE', wn, bn, out, flush=True)
print('pairs checked', n, 'with both diagonals coverable:', found)
