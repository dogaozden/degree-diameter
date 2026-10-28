import sys, itertools, random
sys.path.insert(0, '/home/user/degree-diameter/research/squads/thmfam-r1/c16')
import gen_c16 as g
from screen import score
def orbit_key(X): return tuple(sorted(g.conj_orbit_triples(*X)))
def valid(X): return X != (0,0,0) and (X[0]**2 + X[1]*X[2]) != 1
def pool(R):
    p = {}
    for t in itertools.product(range(-R, R+1), repeat=3):
        if valid(t):
            k = orbit_key(t)
            if len(set(k)) == 3 and k not in p: p[k] = t
    return list(p.items())
mode = sys.argv[1]
if mode == 'd7d8':
    orbs = pool(1)
    for f, D in [(1, 7), (2, 8)]:
        res = []
        for (k1, X1), (k2, X2) in itertools.combinations(orbs, 2):
            if set(k1) & set(k2): continue
            m, _ = score(['conic', str(f), ','.join(map(str, X1)), ','.join(map(str, X2)), '{q}'])
            res.append((m if m is not None else 99, X1, X2))
        res.sort()
        print('Delta', D, 'top', res[:5], 'n', len(res), flush=True)
if mode == 'd6r2':
    orbs = pool(2); R = random.Random(7); res = []
    pairs = [(a, b) for a, b in itertools.combinations(orbs, 2) if not (set(a[0]) & set(b[0]))]
    for (k1, X1), (k2, X2) in R.sample(pairs, 150):
        m, _ = score(['conic', '0', ','.join(map(str, X1)), ','.join(map(str, X2)), '{q}'])
        res.append((m if m is not None else 99, X1, X2))
    res.sort(); print('d6 R2 top', res[:5], flush=True)
