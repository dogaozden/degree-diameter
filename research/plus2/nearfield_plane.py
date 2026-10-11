"""The +2 construction in a non-Desarguesian plane: the nearfield plane of order 9.

The proof in REPORT.md uses only incidence axioms, so the construction should work in any
projective plane of order q >= 4.  This checks it in the plane coordinatised by the Dickson
nearfield of order 9 (x o m = x*m if m is a square, x^3*m otherwise).  A plane coordinatised by
a proper nearfield is not Desarguesian.
"""
import itertools
import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from construction import build, lib  # noqa: E402

q = 9
F = lib.GF(q)
squares = {F.mul(x, x) for x in range(1, q)}


def nf(x, m):
    """Dickson nearfield product of order 9."""
    return F.mul(x, m) if (m == 0 or m in squares) else F.mul(F.pow(x, 3), m)


# a proper nearfield: some product is not the field product, and it is not commutative
assert any(nf(x, m) != F.mul(x, m) for x in range(q) for m in range(q))
assert any(nf(x, m) != nf(m, x) for x in range(q) for m in range(q))
# associative, so a nearfield; a finite division ring would be a field (Wedderburn)
assert all(nf(nf(x, y), z) == nf(x, nf(y, z)) for x in range(q) for y in range(q) for z in range(q))


def plane(mul):
    """Affine plane y = mul(x, m) + b, x = c, completed projectively."""
    pts = {('a', x, y): i for i, (x, y) in enumerate(itertools.product(range(q), repeat=2))}
    for m in range(q):
        pts[('inf', m)] = len(pts)
    pts[('inf', 'v')] = len(pts)
    lines = []
    for m in range(q):
        for b in range(q):
            L = {pts[('a', x, F.add(mul(x, m), b))] for x in range(q)} | {pts[('inf', m)]}
            lines.append(frozenset(L))
    for c in range(q):
        lines.append(frozenset({pts[('a', c, y)] for y in range(q)} | {pts[('inf', 'v')]}))
    lines.append(frozenset(pts[('inf', m)] for m in list(range(q)) + ['v']))
    return list(range(len(pts))), lines


def is_projective_plane(points, lines):
    if any(len(L) != q + 1 for L in lines) or len(lines) != len(points):
        return False
    for L1, L2 in itertools.combinations(lines, 2):
        if len(L1 & L2) != 1:
            return False
    return True


for name, mul in (('x o m', nf), ('m o x', lambda x, m: nf(m, x))):
    points, lines = plane(mul)
    if not is_projective_plane(points, lines):
        print(f'{name}: not a projective plane')
        continue
    print(f'{name}: projective plane of order 9 (nearfield, non-Desarguesian)')
    rng = random.Random(1)
    bad = 0
    for t in range(200):
        ell = rng.randrange(len(lines))
        A = rng.choice(sorted(set(points) - lines[ell]))
        on = sorted(lines[ell])
        rng.shuffle(on)
        n, e = build(points, lines, q, A, ell, on[0], on[1:5])
        bad += not lib.is_valid(n, e, q + 2, 3)
    print(f'  200 random frames (A, ell, P, X0, X1, Xa, Xc): n = {n}, invalid: {bad}')
