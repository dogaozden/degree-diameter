# Generalized quadrangle W(5) = GQ(5,5) incidence graph as base of a Z_m lift.
# Base: 156 points, 156 lines (t.i. lines of symplectic W(3,5)), degree 6 incidence,
# plus 2 random perfect matchings (points->lines) with random Z_m voltages (degree 8).
# Usage: python3 gq_base.py m seed mode > base.txt   (mode: inc0 = zero incidence voltages, rnd = all random)
import sys, random, itertools
q = 5
m = int(sys.argv[1]); seed = int(sys.argv[2]); mode = sys.argv[3] if len(sys.argv) > 3 else 'inc0'
rng = random.Random(seed)
def B(x, y):
    return (x[0]*y[1] - x[1]*y[0] + x[2]*y[3] - x[3]*y[2]) % q
def norm(v):
    for c in v:
        if c % q:
            inv = pow(c, q-2, q)
            return tuple((u*inv) % q for u in v)
    return None
pts = sorted({norm(v) for v in itertools.product(range(q), repeat=4) if any(v)})
assert len(pts) == 156
lines = set()
for p in pts:
    for r in pts:
        if p < r and B(p, r) == 0:
            # span of p,r: all points on the line
            L = set()
            for a, b in itertools.product(range(q), repeat=2):
                if a or b:
                    L.add(norm(tuple((a*p[i] + b*r[i]) % q for i in range(4))))
            lines.add(frozenset(L))
lines = sorted(sorted(L) for L in lines)
assert len(lines) == 156, len(lines)
pid = {p: i for i, p in enumerate(pts)}
edges = []
inc = set()
for li, L in enumerate(lines):
    for p in L:
        inc.add((pid[p], li))
def vol():
    return 0 if mode == 'inc0' else rng.randrange(m)
for (a, b) in sorted(inc):
    edges.append((a, b, vol()))
# two random perfect matchings between points and lines avoiding incidences (retry on clash)
used = set(inc)
for _ in range(2):
    while True:
        perm = list(range(156)); rng.shuffle(perm)
        if all((a, perm[a]) not in used for a in range(156)) and len({perm[a] for a in range(156)}) == 156:
            break
    # also avoid repeated matched pairs with the previous matching
    for a in range(156):
        used.add((a, perm[a]))
        edges.append((a, perm[a], rng.randrange(m)))
print(156, 156, m)
for a, b, v in edges:
    print(a, b, v)
