"""The generalized quadrangle P(W(q),x) of order (q-1, q+1) (for q odd this is the Ahrens-Szekeres GQ AS(q)).

W(q): points of PG(3,q), lines = totally isotropic lines of f(u,v) = u0v1 - u1v0 + u2v3 - u3v2.
Payne derivation at x = (1,0,0,0): x^perp is the plane v1 = 0.
  points: the q^3 points off x^perp, written (a, b, c) for the vector (a, 1, b, c);
  lines : (A) the affine part of each t.i. line meeting x^perp in a point p != x   (q^3 + q^2 lines)
          (B) the affine part of each line of PG(3,q) through x not in x^perp       (q^2 lines, "a varies")
Every line has q points and every point is on q+2 lines.

Coordinates used by the search code: for w = (b,c) in AG(2,q) and a in GF(q) the point is (a, w).
A type (A) line in direction d = (p2,p3) through (a0, w0) is {(a0 + l*D, w0 + l*d) : l}, D = det(w0, d) = b p3 - c p2
(D is constant along the bc-line). A type (B) line is {(a, w) : a} for fixed w.

python3 as_gq.py q    builds, checks the GQ axioms and the incidence graph (girth 8, diameter 4), prints counts.
"""
import itertools
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'problems' / 'bipartite_dd'))
import lib  # noqa: E402


def build(q):
    """Return (F, pts, lines): pts a list of (a,b,c); lines a list of sorted point-index tuples."""
    F = lib.GF(q)
    pts = [(a, b, c) for a in range(q) for b in range(q) for c in range(q)]
    idx = {p: i for i, p in enumerate(pts)}
    # directions in the bc-plane: projective points (p2,p3)
    dirs = [(0, 1)] + [(1, t) for t in range(q)]
    lines = set()
    for (a, b, c) in pts:
        for (p2, p3) in dirs:
            D = F.sub(F.mul(b, p3), F.mul(c, p2))
            L = tuple(sorted(idx[(F.add(a, F.mul(l, D)), F.add(b, F.mul(l, p2)), F.add(c, F.mul(l, p3)))]
                             for l in range(q)))
            lines.add(L)
    for b in range(q):
        for c in range(q):
            lines.add(tuple(sorted(idx[(a, b, c)] for a in range(q))))
    lines = sorted(lines)
    return F, pts, lines


def check_gq(q, pts, lines):
    """Check the GQ axioms of order (q-1, q+1) by brute force."""
    n = len(pts)
    assert n == q ** 3 and len(lines) == (q + 2) * q * q, (n, len(lines))
    assert all(len(L) == q for L in lines)
    on = [[] for _ in range(n)]
    for j, L in enumerate(lines):
        for p in L:
            on[p].append(j)
    assert all(len(o) == q + 2 for o in on)
    # two points on at most one line
    seen = set()
    for L in lines:
        for pr in itertools.combinations(L, 2):
            assert pr not in seen
            seen.add(pr)
    # collinearity sets
    coll = [set() for _ in range(n)]
    for L in lines:
        for p in L:
            coll[p].update(L)
    # GQ axiom: point p not on line L is collinear with exactly one point of L
    for j, L in enumerate(lines):
        Ls = set(L)
        for p in range(n):
            if p in Ls:
                continue
            k = sum(1 for r in L if r in coll[p])
            assert k == 1, (p, j, k)
    return on


def incidence_edges(n, lines):
    return [(p, n + j) for j, L in enumerate(lines) for p in L]


if __name__ == '__main__':
    q = int(sys.argv[1])
    F, pts, lines = build(q)
    check_gq(q, pts, lines)
    n = len(pts)
    N = n + len(lines)
    edges = incidence_edges(n, lines)
    ok = lib.is_valid(N, edges, q + 2, 4)
    print(f'q={q}: {n} points, {len(lines)} lines, GQ axioms ok; incidence graph valid (deg<={q+2}, D=4): {ok}')
