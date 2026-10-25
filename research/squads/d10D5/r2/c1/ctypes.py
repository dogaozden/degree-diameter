import sys, random, math
sys.path.insert(0, '.')
from sym import *
fn = sys.argv[1]; seed = int(sys.argv[2]); tries = int(sys.argv[3])
rng = random.Random(seed)
q, N, lines, lof, coords = load_all(fn)
index = {c: i for i, c in enumerate(coords)}
lidx = {frozenset(ps): l for l, ps in enumerate(lines)}
def pcomp(a, b): return [a[b[i]] for i in range(len(b))]
def ppow(a, e):
    r = list(range(len(a))); base = a[:]
    while e:
        if e & 1: r = pcomp(base, r)
        base = pcomp(base, base); e >>= 1
    return r
def porder(a): return math.lcm(*cycle_type(a).keys())
seen = {}
for t in range(tries):
    Mx = random_elem(rng)
    pp = perm_points(Mx, coords, index)
    o = porder(pp)
    for d in [2,4,5,8,10]:
        if o % d == 0:
            h = ppow(pp, o // d)
            ct = cycle_type(h)
            key = (d, tuple(sorted(ct.items())))
            if key not in seen:
                pl = perm_lines(h, lines, lidx); cl = cycle_type(pl)
                seen[key] = tuple(sorted(cl.items()))
                print('order', d, 'pts', sorted(ct.items()), 'lines', sorted(cl.items()), flush=True)
