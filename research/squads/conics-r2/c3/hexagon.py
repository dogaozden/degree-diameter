"""Split Cayley hexagon H(q), q prime, as a point-line incidence graph.

normalize, quadric_points and hexagon are copied from research/gh6/gh_build.py (the Mac-only `import lib`
line and the JSON writer are left out). incidence_graph is new here.
Points: all points of X0*X4 + X1*X5 + X2*X6 = X3^2 in PG(6,q). Lines: totally singular lines whose Grassmann
coordinates satisfy Tits' six equations (p_ij = x_i y_j - x_j y_i):
  p12 = p34, p54 = p32, p20 = p35, p65 = p30, p01 = p36, p46 = p31.
"""
import itertools

import numpy as np


def normalize(v, q):
    """Scale v so its first nonzero coordinate is 1 (q prime)."""
    for x in v:
        if x % q:
            s = pow(x, q - 2, q)
            return tuple((s * c) % q for c in v)
    raise ValueError('zero vector')


def quadric_points(q):
    pts = []
    for v in itertools.product(range(q), repeat=7):
        if next((c for c in v if c), 0) != 1:
            continue
        if (v[0] * v[4] + v[1] * v[5] + v[2] * v[6] - v[3] * v[3]) % q:
            continue
        pts.append(v)
    return pts


def hexagon(q):
    P = quadric_points(q)
    N = len(P)
    assert N == (q ** 6 - 1) // (q - 1), N
    index = {v: i for i, v in enumerate(P)}
    Pa = np.array(P, dtype=np.int64)
    lines = {}
    line_list = []
    for i in range(N):
        x = P[i]
        xa = Pa[i]

        def pl(a, b):
            return (xa[a] * Pa[:, b] - xa[b] * Pa[:, a]) % q

        polar = (xa[0] * Pa[:, 4] + xa[4] * Pa[:, 0] + xa[1] * Pa[:, 5] + xa[5] * Pa[:, 1]
                 + xa[2] * Pa[:, 6] + xa[6] * Pa[:, 2] - 2 * xa[3] * Pa[:, 3]) % q
        ok = (polar == 0)
        ok &= pl(1, 2) == pl(3, 4)
        ok &= pl(5, 4) == pl(3, 2)
        ok &= pl(2, 0) == pl(3, 5)
        ok &= pl(6, 5) == pl(3, 0)
        ok &= pl(0, 1) == pl(3, 6)
        ok &= pl(4, 6) == pl(3, 1)
        ok[i] = False
        for j in np.nonzero(ok)[0]:
            y = P[j]
            members = {i, int(j)}
            for a in range(q):
                members.add(index[normalize(tuple((x[k] + a * y[k]) % q for k in range(7)), q)])
            if len(members) != q + 1:
                raise AssertionError(f'line with {len(members)} points')
            key = frozenset(members)
            if key not in lines:
                lines[key] = len(line_list)
                line_list.append(sorted(members))
    return N, line_list


def incidence_graph(q):
    """Return (N, L, lines, adj). Vertices 0..N-1 are points, N..N+L-1 are lines (line k is vertex N+k)."""
    N, lines = hexagon(q)
    L = len(lines)
    adj = [[] for _ in range(N + L)]
    for k, pts in enumerate(lines):
        for p in pts:
            adj[p].append(N + k)
            adj[N + k].append(p)
    return N, L, lines, adj
