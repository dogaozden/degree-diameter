r"""Extra check for Section 3 of SYNTHETIC.tex: the exact whisker set for even q (POLISHED.md
Theorem 6.14) in H(4), and the doubling with levels.  Characteristic 2: Q(6,q): X0X4+X1X5+X2X6+X3^2,
Pi_z: X3 = X0 + delta X4 + alpha X2 + beta X5, Tr(delta) = 1.
Run: python3 check_d6_even.py
"""
import itertools
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parents[1] / 'plus2' / 'coords'))
import coords  # noqa: E402  (GF(q))
from incidence import Structure, double_levels  # noqa: E402

q = 4
F = coords.GF(q)
add, mul, inv = F.add, F.mul, F.inv


def lin(*terms):
    s = 0
    for t in terms:
        s = add(s, t)
    return s


def norm(v):
    i = next(i for i in range(7) if v[i])
    c = inv(v[i])
    return tuple(mul(c, x) for x in v)


def Qf(x):
    return lin(mul(x[0], x[4]), mul(x[1], x[5]), mul(x[2], x[6]), mul(x[3], x[3]))


def B(x, y):
    return lin(mul(x[0], y[4]), mul(x[4], y[0]), mul(x[1], y[5]), mul(x[5], y[1]), mul(x[2], y[6]), mul(x[6], y[2]))


pts = [v for v in itertools.product(range(q), repeat=7) if any(v) and norm(v) == v and Qf(v) == 0]
assert len(pts) == (q ** 6 - 1) // (q - 1)


def tits(x, y):
    p = lambda i, j: add(mul(x[i], y[j]), mul(x[j], y[i]))   # char 2: minus = plus
    return (p(1, 2) == p(3, 4) and p(5, 4) == p(3, 2) and p(2, 0) == p(3, 5) and p(6, 5) == p(3, 0)
            and p(0, 1) == p(3, 6) and p(4, 6) == p(3, 1))


lines = set()
for x, y in itertools.combinations(pts, 2):
    if B(x, y) == 0 and tits(x, y):
        lines.add(frozenset({x, y} | {norm(tuple(add(mul(a, u), w) for u, w in zip(x, y))) for a in range(1, q)}))
lines = sorted(lines, key=sorted)
assert len(lines) == len(pts), len(lines)
names = [('H', i) for i in range(len(lines))]
H = Structure(pts, names, {(p, names[i]) for i, L in enumerate(lines) for p in L})
assert all(len(H.lines_on[p]) == q + 1 for p in pts)

# trace and delta
tr = lambda z: lin(z, mul(z, z))           # GF(4): Tr(z) = z + z^2
delta = next(d for d in range(q) if tr(d) == 1)
FAIL = []


def check(c, m):
    if not c:
        FAIL.append(m)
        print('FAIL:', m)


def inPi(x, al=0, be=0):
    return x[3] == lin(x[0], mul(delta, x[4]), mul(al, x[2]), mul(be, x[5]))


v = next(n for i, n in enumerate(names) if all(p[k] == 0 for p in lines[i] for k in (0, 2, 3, 4, 5)))
Spts = {p for p in pts if inPi(p)}
S = [L for L in H.lines if H.pts_on[L] <= Spts]
check(len(S) == q ** 3 + 1 and v in S, 'spread of size q^3+1 containing v')
dv = H.distances_from(v)
free = {p for p in pts if p not in Spts and dv[p] == 5}
check(len(free) == q ** 3 * (q * q - 1), 'free points')

# c0, c1 with G zero-free
def G(a, b, c0, c1):
    return add(mul(lin(mul(c0, a), mul(c1, b)), lin(mul(a, a), mul(a, b), mul(delta, mul(b, b)))), mul(b, mul(b, b)))
c0, c1 = next((c0, c1) for c0 in range(1, q) for c1 in range(q)
              if all(G(a, b, c0, c1) for a in range(q) for b in range(q) if (a, b) != (0, 0)))
W = set()
for al in range(q):
    for be in range(q):
        if (al, be) == (0, 0):
            continue
        for i, L in enumerate(lines):
            if names[i] == v or not all(inPi(x, al, be) for x in L):
                continue
            X = [x for x in L if inPi(x)]
            assert len(X) == 1
            X = X[0]
            num = lin(mul(X[2], X[3]), mul(X[2], X[4]), mul(X[4], X[5]))
            den = lin(mul(delta, mul(X[2], X[2])), mul(X[2], X[5]), mul(X[5], X[5]))
            Fz = mul(G(al, be, c0, c1), inv(lin(mul(al, al), mul(al, be), mul(delta, mul(be, be)))))
            if mul(num, inv(den)) == Fz:
                W.add(names[i])
check(len(W) == q * q * (q * q - 1), '|W| = q^2(q^2-1)')
check(all(sum(1 for L in W if p in H.pts_on[L]) == 1 for p in free), 'W is an exact whisker set (even q formula)')
Sset = set(S)
Lv = [L for L in H.lines if L != v and H.pts_on[L] & H.pts_on[v]]
level = {}
for x in [*Sset, *Spts, *Lv, *W]:
    level[x] = 0
for x in [*Sset, *H.pts_on[v]]:
    level[x] = 1
level[v] = 2
D = double_levels(H, level, 2)
N = len(pts)
n = len(D.points) + len(D.lines)
check(n == 2 * N + 2 * q ** 4 + 4 * q ** 3 + 4 * q + 10, 'doubled count 2N + 2q^4 + 4q^3 + 4q + 10')
md = max(max(D.point_degree(x) for x in D.points), max(D.line_degree(L) for L in D.lines))
check(md == q + 2, 'max degree q+2')
print(f'H({q}): {N} points; (c0,c1) = ({c0},{c1}); |W| = {len(W)}; doubled: {n} elements, max degree {md}')
d = D.diameter()
check(d == 6, f'diameter 6 (got {d})')
print('ALL CHECKS PASSED' if not FAIL else f'{len(FAIL)} FAILURES')
sys.exit(0 if not FAIL else 1)
