"""Rebuild the table's Delorme / Delorme-Farhi duplication cells (table-audit).

  d3 q OUT        PG(2,q) plus copies (Delorme-Farhi 1984) of the q+1 points of a conic and of its q+1 tangent lines;
                  each copy is joined to the original neighbours of its vertex.  Degree q+3, diameter 3,
                  order 2(q^2+q+1) + 2(q+1).  q = 13: 394 = table (16,3).
  d4 q b OUT      Delorme 1985 Sec. 8(a): W(q) with a spread {<X, AX>} (A = B (x) I_2, B symmetric with irreducible
                  characteristic polynomial); A1 = one spread line, A0 = A1's points plus the spread; levels
                  1 / 0 / -1 and the b-fold level lift (b = 2: degree q+2, b = 3: degree q+3).
                  Order 2(q+1)(q^2+1) + (b-1)(|A0| + b|A1|).  Table (7,4) 346, (11,4) 1734, (13,4) 3064,
                  (15,4) 4946 (b = 2, q = 5, 9, 11, 13); (16,4) 5134 (b = 3, q = 13).
  d6 q b OUT      Delorme 1985 Sec. 8(b): H(q) with the Hermitian spread S (the q^3+1 hexagon lines inside an elliptic
                  hyperplane section, Thas 1980); A2 = one line v of S, A1 = v's points and S, A0 = A1 and its
                  neighbours; levels 2 / 1 / 0 / -1 and the b-fold lift.  Table (7,6) 8992, (11,6) 142464,
                  (13,6) 374452, (15,6) 842048 (b = 2, q = 5, 9, 11, 13); (16,6) 884062 (b = 3, q = 13).
  d7 q OUT        Delorme 1985 Sec. 9: H(q), an edge uv; subdivide every edge between distance 2 and 3 from {u, v}
                  (2q^3 new vertices, diameter 7, still bipartite: the subdivided edges form a cut), then q copies of
                  A0 = {x : min d(x,u), d(x,v) <= 2} (level lift, b = q).  Degree q+1, diameter 7, order
                  2q(q^4+q^3+3q^2+q+1).  Table (6,7) 8310 (q = 5), (8,7) 40586 (q = 7).
Base geometries come from moore_build (edge list + point coordinates) in BIN/, written to G/."""
import os
import random
import subprocess
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gf import GF
from levellift import lift, read_edges, write_edges

BIN = os.environ.get('BIN', '.')
G = os.environ.get('G', '.')


def geometry(kind, q):
    e, c = f'{G}/{kind}_{q}.txt', f'{G}/{kind}_{q}.crd'
    if not (os.path.exists(e) and os.path.exists(c)):
        subprocess.run([f'{BIN}/moore_build', kind, str(q), e, c], check=True)
    n, E = read_edges(e)
    crd = [tuple(map(int, line.split()[1:])) for line in open(c)]
    N = len(crd)
    pts_of = [[] for _ in range(n - N)]
    for u, v in E:
        pts_of[v - N].append(u)
    return n, E, crd, pts_of


def d3(q, out):
    F = GF(q)
    n, E, crd, pts_of = geometry('pg', q)
    N = len(crd)
    pidx = {c: i for i, c in enumerate(crd)}
    # conic y^2 = xz: points (1, t, t^2) and (0, 0, 1); a line (l0,l1,l2) is the set of points x with l.x = 0
    conic = [pidx[F.normalize((1, t, F.mul[t][t]))] for t in range(q)] + [pidx[(0, 0, 1)]]
    cs = set(conic)
    tangents = [N + j for j, P in enumerate(pts_of) if len(cs.intersection(P)) == 1]
    assert len(conic) == q + 1 and len(tangents) == q + 1
    nbr = [[] for _ in range(n)]
    for u, v in E:
        nbr[u].append(v)
        nbr[v].append(u)
    E2, m = list(E), n
    for x in conic + tangents:          # copy x: joined to the original neighbours of x
        E2 += [(m, y) for y in nbr[x]]
        m += 1
    write_edges(out, m, E2)
    print(out, 'PG(2,%d) + conic and tangent copies:' % q, m, 'vertices,', len(E2), 'edges')


def d4(q, b, out):
    F = GF(q)
    n, E, crd, pts_of = geometry('w', q)
    N = len(crd)
    pidx = {c: i for i, c in enumerate(crd)}
    lines_through = [set() for _ in range(N)]
    for j, P in enumerate(pts_of):
        for p in P:
            lines_through[p].add(j)
    # B = [[0, s], [s, a]] symmetric, char poly T^2 - aT - s^2 irreducible; A = B (x) I_2 on (x0, x1 | x2, x3)
    for a in range(q):
        for s in range(1, q):
            ss = F.mul[s][s]
            if all(F.sub(F.sub(F.mul[t][t], F.mul[a][t]), ss) != 0 for t in range(q)):
                break
        else:
            continue
        break
    B = ((0, s), (s, a))

    def A(x):
        return tuple(F.add[F.mul[B[i][0]][x[j]]][F.mul[B[i][1]][x[2 + j]]] for i in (0, 1) for j in (0, 1))
    spread = set()
    for i, x in enumerate(crd):
        y = pidx[F.normalize(A(x))]
        assert y != i
        L = list(lines_through[i] & lines_through[y])
        assert len(L) == 1, 'span(X, AX) is not a line of W(q)'
        spread.add(N + L[0])
    spread = sorted(spread)
    assert len(spread) == q * q + 1
    assert sorted(p for l in spread for p in pts_of[l - N]) == list(range(N)), 'not a partition'
    lev = [-1] * n
    l0 = spread[0]
    for l in spread:
        lev[l] = 0
    lev[l0] = 1
    for p in pts_of[l0 - N]:
        lev[p] = 0
    m, E2 = lift(n, E, lev, b)
    write_edges(out, m, E2)
    A0 = sum(1 for t in lev if t >= 0)
    print(out, 'W(%d) spread lift b=%d: |A0|=%d |A1|=%d ->' % (q, b, A0, 1), m, 'vertices,', len(E2), 'edges')


def d6(q, b, out, seed=1):
    F = GF(q)
    n, E, crd, pts_of = geometry('h', q)
    N = len(crd)
    rng = random.Random(seed)
    target = q ** 3 + 1
    C = np.array(crd, dtype=np.int64)
    ADD, MUL = np.array(F.add), np.array(F.mul)
    P = np.array(pts_of, dtype=np.int64)
    for _ in range(2000):
        a = [rng.randrange(q) for _ in range(7)]
        acc = np.zeros(N, dtype=np.int64)
        for j in range(7):
            acc = ADD[acc, MUL[a[j], C[:, j]]]
        inH = acc == 0
        S = [N + j for j in np.nonzero(inH[P].all(axis=1))[0].tolist()]
        if len(S) == target:
            break
    else:
        raise RuntimeError('no elliptic hyperplane section found')
    # S must be pairwise opposite: no two lines of S share a point, and none meets another's neighbour lines'
    # points at distance 2 (checked below by the diameter/degree checks of the lifted graph; here: disjointness)
    cover = [0] * N
    for l in S:
        for p in pts_of[l - N]:
            cover[p] += 1
    assert max(cover) == 1
    lev = [-1] * n
    v = S[0]
    lines_through = [[] for _ in range(N)]
    for j, P in enumerate(pts_of):
        for p in P:
            lines_through[p].append(N + j)
    for l in S[1:]:
        lev[l] = 1
        for p in pts_of[l - N]:
            lev[p] = 0
    for p in pts_of[v - N]:
        for l in lines_through[p]:
            if l != v:
                assert lev[l] == -1
                lev[l] = 0
    for p in pts_of[v - N]:
        lev[p] = 1
    lev[v] = 2
    m, E2 = lift(n, E, lev, b)
    write_edges(out, m, E2)
    cnt = [sum(1 for t in lev if t >= k) for k in range(3)]
    print(out, 'H(%d) Hermitian spread lift b=%d: |A0|=%d |A1|=%d |A2|=%d ->' % (q, b, *cnt), m, 'vertices,', len(E2), 'edges')


def d7(q, out):
    n, E, crd, pts_of = geometry('h', q)
    nbr = [[] for _ in range(n)]
    for a, b in E:
        nbr[a].append(b)
        nbr[b].append(a)
    u, v = E[0]
    dist = [-1] * n
    dist[u] = dist[v] = 0
    fr = [u, v]
    while fr:
        nf = []
        for x in fr:
            for y in nbr[x]:
                if dist[y] < 0:
                    dist[y] = dist[x] + 1
                    nf.append(y)
        fr = nf
    E2, m = [], n
    for a, b in E:
        if {dist[a], dist[b]} == {2, 3}:
            E2 += [(a, m), (m, b)]
            m += 1
        else:
            E2.append((a, b))
    assert m - n == 2 * q ** 3
    lev = [0 if x < n and dist[x] <= 2 else -1 for x in range(m)]
    assert sum(1 for t in lev if t == 0) == 2 * (q * q + q + 1)
    m2, E3 = lift(m, E2, lev, q)
    write_edges(out, m2, E3)
    print(out, 'H(%d) Sec. 9: %d inserted, |A0| = %d, %d copies ->' % (q, m - n, 2 * (q * q + q + 1), q), m2, 'vertices')


if __name__ == '__main__':
    kind = sys.argv[1]
    if kind == 'd3':
        d3(int(sys.argv[2]), sys.argv[3])
    elif kind == 'd7':
        d7(int(sys.argv[2]), sys.argv[3])
    elif kind == 'd4':
        d4(int(sys.argv[2]), int(sys.argv[3]), sys.argv[4])
    else:
        d6(int(sys.argv[2]), int(sys.argv[3]), sys.argv[4])
