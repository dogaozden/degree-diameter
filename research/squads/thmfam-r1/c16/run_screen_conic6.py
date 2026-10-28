import sys, itertools
sys.path.insert(0, '/home/user/degree-diameter/research/squads/thmfam-r1/c16')
import gen_c16 as g
from screen import score
def orbit_key(X):
    return tuple(sorted(g.conj_orbit_triples(*X)))
def valid(X):
    x, y, z = X
    return (x, y, z) != (0, 0, 0) and (x*x + y*z) != 1
R = int(sys.argv[1])
pool = {}
for t in itertools.product(range(-R, R+1), repeat=3):
    if valid(t):
        k = orbit_key(t)
        if len(set(k)) == 3 and k not in pool:
            pool[k] = t
orbs = list(pool.items())
print('orbits', len(orbs), file=sys.stderr)
res = []
for (k1, X1), (k2, X2) in itertools.combinations(orbs, 2):
    if set(k1) & set(k2):
        continue
    args = ['conic', '0', ','.join(map(str, X1)), ','.join(map(str, X2)), '{q}']
    m, _ = score(args)
    res.append((m if m is not None else 99, X1, X2))
res.sort()
for r in res[:12]:
    print(r)
print('n', len(res))
