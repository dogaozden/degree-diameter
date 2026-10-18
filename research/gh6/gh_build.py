"""Split Cayley hexagon H(q) as a point-line incidence graph (q prime, plain mod-q arithmetic).

Points: all points of the parabolic quadric X0*X4 + X1*X5 + X2*X6 = X3^2 in PG(6,q).
Lines: the totally singular lines whose Grassmann coordinates satisfy Tits' six equations
  p12 = p34, p54 = p32, p20 = p35, p65 = p30, p01 = p36, p46 = p31   (p_ij = x_i y_j - x_j y_i).
Output: hex/hexagon_q{q}.json = {"q", "points", "lines": [[point ids of line k], ...]}, points 0..N-1.
Usage: python3 gh_build.py q
"""
import itertools
import json
import sys
from collections import deque
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, '/Users/dogaozden/AI_Projects/degree-diameter/problems/bipartite_dd')
import lib  # noqa: E402

import numpy as np  # noqa: E402


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


def girth(n, edges):
    """Exact girth by BFS from every vertex (non-tree edge gives a cycle through the root)."""
    adj = lib.adjacency(n, edges)
    best = 10 ** 9
    for s in range(n):
        dist = [-1] * n
        par = [-1] * n
        dist[s] = 0
        dq = deque([s])
        while dq:
            u = dq.popleft()
            if 2 * dist[u] >= best:
                break
            for w in adj[u]:
                if dist[w] < 0:
                    dist[w] = dist[u] + 1
                    par[w] = u
                    dq.append(w)
                elif par[u] != w:
                    best = min(best, dist[u] + dist[w] + 1)
    return best


def check(q):
    N, lines = hexagon(q)
    L = len(lines)
    through = [0] * N
    for Ln in lines:
        for p in Ln:
            through[p] += 1
    checks = {
        'points': N, 'lines': L,
        'lines_equal_points': L == N,
        'every_line_q+1_points': all(len(Ln) == q + 1 for Ln in lines),
        'every_point_on_q+1_lines': all(t == q + 1 for t in through),
    }
    edges = [(p, N + k) for k, Ln in enumerate(lines) for p in Ln]
    checks['diameter6_degree_q+1'] = lib.is_valid(2 * N, edges, q + 1, 6)
    checks['girth'] = girth(2 * N, edges)
    checks['girth_is_12'] = checks['girth'] == 12
    return N, lines, checks


if __name__ == '__main__':
    q = int(sys.argv[1])
    N, lines, checks = check(q)
    for k, v in checks.items():
        print(f'{k}: {v}', flush=True)
    ok = checks['lines_equal_points'] and checks['every_line_q+1_points'] and \
        checks['every_point_on_q+1_lines'] and checks['diameter6_degree_q+1'] and checks['girth_is_12']
    print(f'q={q}: H(q) checks {"PASSED" if ok else "FAILED"}', flush=True)
    if ok:
        out = HERE / 'hex' / f'hexagon_q{q}.json'
        out.write_text(json.dumps({'q': q, 'points': N, 'lines': lines}))
        print('wrote', out, flush=True)
