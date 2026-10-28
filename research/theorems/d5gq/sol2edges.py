"""Independent rebuild of a typed level graph with hubs from its solution file (Definitions 2.1 and 3.1 of
D5_QUADRANGLE.md), without levels.py.  The solution file must contain W(q) explicitly ('W_points': coordinates of the
points of PG(3,q); 'W_lines': point ids of each totally isotropic line); this script re-checks that they form W(q) for
the form x0y2 + x1y3 - x2y0 - x3y1, then takes G = Q(4,q) = W(q)^D (point i of G = line i of W, line j of G = point j
of W).  Vertex (element e, level j) gets id j*2N + e, where e < N is a point of G and N + l is line l of G; hubs follow
(B-hubs, then A-hubs).

usage: python3 sol2edges.py SOLUTION.json OUT.edges  [COMPARE.edges(.gz)]"""
import sys, json, gzip, itertools
sys.path.insert(0, __import__('os').path.join(__import__('os').path.dirname(__file__), '..', 'chartlift'))
from gf import GF

sol = json.load(open(sys.argv[1]))
q = sol['q']; F = GF(q); types = sol['types']; arcs = [tuple(a) for a in sol['arcs']]
pts = [tuple(p) for p in sol['W_points']]; wl = [list(l) for l in sol['W_lines']]
N = len(pts)
assert N == (q + 1) * (q * q + 1) and len(wl) == N
def w(x, y):
    a = F.add[F.mul[x[0]][y[2]]][F.mul[x[1]][y[3]]]; b = F.add[F.mul[x[2]][y[0]]][F.mul[x[3]][y[1]]]
    return F.sub[a][b]
# W(q) check: distinct normalized points, each line = q+1 pairwise orthogonal points, each pair of points on <= 1 line,
# each point on q+1 lines
assert len(set(pts)) == N and all(next(c for c in p if c) == 1 for p in pts)
on = [[] for _ in range(N)]
seen = set()
for li, l in enumerate(wl):
    assert len(l) == q + 1 and len(set(l)) == q + 1
    for a, b in itertools.combinations(l, 2):
        assert w(pts[a], pts[b]) == 0 and (a, b) not in seen
        seen.add((a, b)); seen.add((b, a))
    for a in l: on[a].append(li)
assert all(len(x) == q + 1 for x in on)
# G = W^D: points of G = W-lines, lines of G = W-points; G-line j contains the G-points on[j]
Glines = on                         # G-line j -> G-points (W-lines through W-point j)
L = len(types)
def eid(kind, i): return i if kind == 'P' else N + i
A = lambda t: 'P' if t == 'H' else 'L'
B = lambda t: 'L' if t == 'H' else 'P'
edges = set()
for j in range(L):
    for l in range(N):
        for p in Glines[l]:
            edges.add((j * 2 * N + p, j * 2 * N + N + l))
nf = sol.get('nonfriendly', {})
freed = {}
for (u, v) in arcs:
    if types[u] != types[v]:
        M = list(range(N))
        if types[u] == 'H': R = set(sol['ovoid_Q4'])
        else: R = set(sol['T'] if (u, v) != (6, 2) else sol.get('T2', sol['T'])) if 'T' in sol else set(sol['pspread_Q4'])
    else:
        d = nf['%d,%d' % (u, v)]; M = d['M']; R = set(d['R'])
    assert sorted(M) == list(range(N))
    freed[(u, v)] = (M, R)
    for a in range(N):
        if a in R: continue
        edges.add((u * 2 * N + eid(A(types[u]), a), v * 2 * N + eid(B(types[v]), M[a])))
nv = L * 2 * N
KB, KA = sol['K_B'], sol['K_A']
used = set()
for h, slots in enumerate(sol['Bhub_slots']):
    assert sorted(s[0] for s in slots) == list(range(L))
    for (j, a, t) in slots:
        t = tuple(t); M, R = freed[t]
        assert t[0] == j and a in R and ('A', t, a) not in used; used.add(('A', t, a))
        edges.add((nv + h, j * 2 * N + eid(A(types[j]), a)))
for g, slots in enumerate(sol['Ahub_slots']):
    assert sorted(s[0] for s in slots) == list(range(L))
    for (j, b, t) in slots:
        t = tuple(t); M, R = freed[t]
        a = [x for x in R if M[x] == b]
        assert t[1] == j and len(a) == 1 and ('B', t, a[0]) not in used; used.add(('B', t, a[0]))
        edges.add((nv + KB + g, j * 2 * N + eid(B(types[j]), b)))
for (h, g) in sol['Y']:
    edges.add((nv + h, nv + KB + g))
n = nv + KB + KA
with open(sys.argv[2], 'w') as f:
    f.write('%d\n' % n)
    for a, b in sorted(edges): f.write('%d %d\n' % (a, b))
print('rebuilt n=%d edges=%d' % (n, len(edges)))
if len(sys.argv) > 3:
    op = gzip.open if sys.argv[3].endswith('.gz') else open
    with op(sys.argv[3], 'rt') as f:
        m = int(f.readline()); E2 = set()
        for line in f:
            a, b = map(int, line.split()); E2.add((min(a, b), max(a, b)))
    E1 = {(min(a, b), max(a, b)) for a, b in edges}
    print('compare with %s: n %s, edge sets %s' % (sys.argv[3], 'equal' if m == n else 'DIFFER', 'equal' if E1 == E2 else 'DIFFER'))
