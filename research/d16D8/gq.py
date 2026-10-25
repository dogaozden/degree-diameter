# gq.py: the symplectic generalized quadrangle W(q) (q prime) and base files for baselift.
#
# Points: points of PG(3,q); lines: totally isotropic lines for B(x,y) = x0y1 - x1y0 + x2y3 - x3y2.
# Incidence graph I: points 0..N-1, lines N..2N-1, (q+1)-regular, diameter 4, girth 8. N = (q+1)(q^2+1).
# W(q) is the GQ testbed for the hexagon problem: I + 2 point-line matchings lifted by Z_m, target diameter 6 = 4 + 2,
# degree q+3, the same as H(q) + 2 matchings at diameter 8.
#
#   python3 gq.py base q m seed OUT     random design: random flag voltages, two random matchings with random voltages
#   python3 gq.py save q OUT.json        point coordinates and the line list (for building structured designs)
# Library: load(q) -> dict(q, N, pts, lines, plines); write_base(fn, V, m, edges)
import sys, json, random

def gq(q):
    pts = []
    for a in range(q):
        for b in range(q):
            for c in range(q):
                pts.append((1, a, b, c))
    for b in range(q):
        for c in range(q):
            pts.append((0, 1, b, c))
    for c in range(q):
        pts.append((0, 0, 1, c))
    pts.append((0, 0, 0, 1))
    idx = {p: i for i, p in enumerate(pts)}
    def norm(v):
        v = [x % q for x in v]
        for x in v:
            if x:
                inv = pow(x, q - 2, q)
                return tuple(y * inv % q for y in v)
        return None
    def B(x, y):
        return (x[0] * y[1] - x[1] * y[0] + x[2] * y[3] - x[3] * y[2]) % q
    lines, seen = [], set()
    for i, x in enumerate(pts):
        perp = [j for j, y in enumerate(pts) if j != i and B(x, pts[j]) == 0]
        done = set()
        for j in perp:
            if j in done:
                continue
            y = pts[j]
            L = sorted(set([i] + [idx[norm([x[t] * l + y[t] for t in range(4)])] for l in range(q)] + [j]))
            for z in L:
                done.add(z)
            key = tuple(L)
            if key not in seen:
                seen.add(key); lines.append(L)
    N = len(pts)
    assert len(lines) == N, (len(lines), N)
    plines = [[] for _ in range(N)]
    for l, L in enumerate(lines):
        assert len(L) == q + 1
        for p in L:
            plines[p].append(l)
    assert all(len(x) == q + 1 for x in plines)
    return dict(q=q, N=N, pts=pts, lines=lines, plines=plines)

_cache = {}
def load(q):
    if q not in _cache:
        _cache[q] = gq(q)
    return _cache[q]

def write_base(fn, V, m, edges):
    with open(fn, 'w') as f:
        f.write('%d %d %d\n' % (V, m, len(edges)))
        f.write(''.join('%d %d %d %d\n' % e for e in edges))

def random_design(q, m, seed, t=2):
    G = load(q); N = G['N']; rnd = random.Random(seed)
    edges = []
    for l, L in enumerate(G['lines']):
        for p in L:
            edges.append((p, N + l, rnd.randrange(m), 1))
    for k in range(t):
        perm = list(range(N)); rnd.shuffle(perm)
        for p in range(N):
            edges.append((p, N + perm[p], rnd.randrange(m), 100 + k))
    return 2 * N, edges

if __name__ == '__main__':
    if sys.argv[1] == 'base':
        q, m, seed, out = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
        V, E = random_design(q, m, seed)
        write_base(out, V, m, E)
    elif sys.argv[1] == 'save':
        q, out = int(sys.argv[2]), sys.argv[3]
        G = load(q)
        json.dump(dict(q=q, N=G['N'], pts=G['pts'], lines=G['lines']), open(out, 'w'))
