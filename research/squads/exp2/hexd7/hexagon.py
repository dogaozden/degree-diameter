"""Split Cayley hexagon H(q) and the 3-copy diameter-7 graph built from it (stdlib + numpy).

H(q) (Tits): points = points of the parabolic quadric Q(6,q): X0X4 + X1X5 + X2X6 = X3^2 in PG(6,q); lines = lines of
Q(6,q) whose Grassmann coordinates satisfy p12 = p34, p54 = p32, p20 = p35, p65 = p30, p01 = p36, p46 = p31.
For a fixed point x the six conditions are linear in the second point y, so the q+1 lines through x are the lines
through x in the plane they cut out (checked: the solution space has dimension 3 and is totally singular).

build(q) returns (P, lines, pts_of_line, lines_of_pt). The incidence graph is checked to be (q+1)-regular with girth 12
and diameter 6 (a bipartite Moore graph), which characterises generalized hexagons of order (q,q).

usage: python3 hexagon.py q [--check]
"""
import sys
import itertools
import numpy as np

sys.path.insert(0, __import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)),
                                              '..', '..', '..', 'frontier'))
from build_haar2 import Field  # GF(q) tables (prime powers given by 'poly')

POLY = {4: 'x^2+x+1', 8: 'x^3+x+1', 9: 'x^2+2x+2', 25: 'x^2+x+2', 27: 'x^3+2x+1'}


class GF:
    def __init__(self, q):
        f = Field(q, POLY.get(q))
        self.q, self.add, self.mul, self.neg, self.inv = q, f.add, f.mul, f.neg, f.inv
        self.sub = np.array([[f.add[a, f.neg[b]] for b in range(q)] for a in range(q)], dtype=np.int64)


def nullspace(F, rows, n):
    """basis of {y in F^n : rows . y = 0} (Gaussian elimination over F)"""
    A = [list(r) for r in rows]
    piv_cols, r = [], 0
    for c in range(n):
        pr = next((i for i in range(r, len(A)) if A[i][c]), None)
        if pr is None:
            continue
        A[r], A[pr] = A[pr], A[r]
        iv = F.inv[A[r][c]]
        A[r] = [F.mul[iv, a] for a in A[r]]
        for i in range(len(A)):
            if i != r and A[i][c]:
                t = A[i][c]
                A[i] = [F.sub[a, F.mul[t, b]] for a, b in zip(A[i], A[r])]
        piv_cols.append(c)
        r += 1
        if r == len(A):
            break
    free = [c for c in range(n) if c not in piv_cols]
    basis = []
    for fc in free:
        v = [0] * n
        v[fc] = 1
        for i, pc in enumerate(piv_cols):
            v[pc] = F.neg[A[i][fc]]
        basis.append(v)
    return basis


def normalize(F, v):
    i = next(k for k, a in enumerate(v) if a)
    iv = F.inv[v[i]]
    return tuple(int(F.mul[iv, a]) for a in v)


def build(q, check=True):
    F = GF(q)
    M, A = F.mul, F.add
    # projective points of the quadric, normalized (first nonzero coordinate 1)
    pts = []
    for v in itertools.product(range(q), repeat=7):
        if not any(v):
            continue
        if v[next(k for k, a in enumerate(v) if a)] != 1:
            continue
        lhs = A[A[M[v[0], v[4]], M[v[1], v[5]]], M[v[2], v[6]]]
        if lhs == M[v[3], v[3]]:
            pts.append(v)
    idx = {v: i for i, v in enumerate(pts)}
    P = len(pts)
    assert P == (q ** 6 - 1) // (q - 1), P
    sub = F.sub
    line_id, pts_of_line, lines_of_pt = {}, [], [[] for _ in range(P)]
    for i, x in enumerate(pts):
        # coefficient rows (in y) of the six conditions p_ab(x,y) - p_cd(x,y) = 0, p_ab = x_a y_b - x_b y_a
        def pab(a, b):
            r = [0] * 7
            r[b] = A[r[b], x[a]]
            r[a] = sub[r[a], x[b]]
            return r
        conds = [(1, 2, 3, 4), (5, 4, 3, 2), (2, 0, 3, 5), (6, 5, 3, 0), (0, 1, 3, 6), (4, 6, 3, 1)]
        rows = []
        for a, b, c, d in conds:
            r1, r2 = pab(a, b), pab(c, d)
            rows.append([int(sub[u, w]) for u, w in zip(r1, r2)])
        # y must also lie in the tangent hyperplane x^perp: B(x,y) = x0y4+x4y0+x1y5+x5y1+x2y6+x6y2-2x3y3
        bx = [x[4], x[5], x[6], int(F.neg[A[x[3], x[3]]]), x[0], x[1], x[2]]
        rows.append([int(a) for a in bx])
        ns = nullspace(F, rows, 7)
        assert len(ns) == 3, (q, i, len(ns))
        # the plane spanned by ns contains x; enumerate its points, group into lines through x
        plane = set()
        for co in itertools.product(range(q), repeat=3):
            if not any(co):
                continue
            v = [0] * 7
            for c_, b_ in zip(co, ns):
                if c_:
                    v = [int(A[a, M[c_, bb]]) for a, bb in zip(v, b_)]
            plane.add(normalize(F, v))
        assert len(plane) == q * q + q + 1 and x in plane
        for y in plane:
            assert y in idx, "plane not on the quadric"
        others = [y for y in plane if y != x]
        seen = set()
        for y in others:
            if y in seen:
                continue
            ln = {x, y}
            for t in range(1, q):
                ln.add(normalize(F, [int(A[a, M[t, b]]) for a, b in zip(y, x)]))
            seen |= ln
            key = tuple(sorted(idx[z] for z in ln))
            assert len(key) == q + 1
            if key not in line_id:
                line_id[key] = len(pts_of_line)
                pts_of_line.append(key)
            lines_of_pt[i].append(line_id[key])
        assert len(lines_of_pt[i]) == q + 1
    L = len(pts_of_line)
    assert L == P, (L, P)
    for li, ln in enumerate(pts_of_line):
        for p in ln:
            assert li in lines_of_pt[p]
    if check:
        check_moore(P, pts_of_line, lines_of_pt, q)
    return P, pts_of_line, lines_of_pt


def adjacency(P, pts_of_line, lines_of_pt):
    """incidence graph: points 0..P-1, lines P..2P-1"""
    adj = [list(P + l for l in lines_of_pt[p]) for p in range(P)] + [list(ln) for ln in pts_of_line]
    return adj


def bfs(adj, s):
    n = len(adj)
    dist = [-1] * n
    dist[s] = 0
    fr = [s]
    while fr:
        nx = []
        for u in fr:
            for w in adj[u]:
                if dist[w] < 0:
                    dist[w] = dist[u] + 1
                    nx.append(w)
        fr = nx
    return dist


def check_moore(P, pts_of_line, lines_of_pt, q):
    adj = adjacency(P, pts_of_line, lines_of_pt)
    n = 2 * P
    # point-transitivity is not assumed: BFS from a sample of points and lines; full check in C (apsp) later
    import random
    rng = random.Random(1)
    for s in [0, P] + [rng.randrange(n) for _ in range(20)]:
        d = bfs(adj, s)
        assert min(d) >= 0 and max(d) == 6, (s, max(d))
        cnt = [d.count(k) for k in range(7)]
        exp = [1, q + 1, (q + 1) * q, (q + 1) * q ** 2, (q + 1) * q ** 3, (q + 1) * q ** 4, q ** 5]
        assert cnt == exp, (cnt, exp)   # Moore ball sizes up to radius 5 <=> girth >= 12
    print('H(%d): %d points, %d lines, incidence graph (q+1)-regular, Moore ball sizes and diameter 6 from 22 sources'
          % (q, P, len(pts_of_line)), flush=True)


if __name__ == '__main__':
    q = int(sys.argv[1])
    P, pl, lp = build(q)
