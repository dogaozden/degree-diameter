#!/usr/bin/env python3
"""Rebuild the (12,7) graph on 664,304 vertices (job cell-12-7) from its definition.

Construction:
  H = split Cayley hexagon H(9) (incidence graph: 66,430 points, 66,430 lines, 10-regular, diameter 6), built by
      research/squads/d12D7-r1/tools/gh_fast.py (points of X0X4+X1X5+X2X6 = X3^2 in PG(6,9), Tits' line equations).
  s1, s2 : points -> lines, two bijections (read from d12D7_n664304.match.gz: line 'p s1(p) s2(p)').
  Polygon cover over Z_5: vertices (x, c), x a point or a line of H, c in Z_5;
      (p, c) ~ (L, c)              for p on L               (hexagon edges, voltage 0)
      (p, c) ~ (s_t(p), c + t)     for t = 1, 2             (the two matchings, voltages 1 and 2)
  This is the table's construction (5 copies of H(9) + 2 matchings, 664,300 vertices, diameter 7).
  Gadget at the point X = 0: delete the 10 edges (X, c) ~ (s_t(X), c + t), add four vertices
      W1, W2 adjacent to (X, c) for c = 0..4, and W1', W2' with W_t' adjacent to (s_t(X), c) for c = 0..4.
  Result: 664,304 vertices, maximum degree 12, bipartite, diameter 7.

Vertex numbering (same as gadget.c): (x, c) -> 5*x + c with points x = 0..P-1 and lines x = P + k; W1, W2, W1', W2'
are 10P, 10P+1, 10P+2, 10P+3. The edge list is written canonically (u < w, sorted).

usage: python3 build_d12D7_n664304.py OUT.edges [MATCH.gz]      prints the sha256 of OUT.edges
       expected sha256 (canonical sorted list): 2eb631995dda1901178b9c425e007d7c1bacfe32b294b00dee0073b45ee12831
Check with research/squads/d12D7-r1/tools/apsp.c (all pairs, no symmetry) or d12D7/opus/symcheck.c (Z5 shift).
"""
import gzip, hashlib, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..', 'd12D7-r1', 'tools'))
from gh_fast import hexagon          # noqa: E402

EXPECTED = '2eb631995dda1901178b9c425e007d7c1bacfe32b294b00dee0073b45ee12831'


def main():
    out = sys.argv[1]
    mfile = sys.argv[2] if len(sys.argv) > 2 else os.path.join(HERE, 'd12D7_n664304.match.gz')
    P, L = hexagon(9)
    s = {1: [0] * P, 2: [0] * P}
    with gzip.open(mfile, 'rt') as f:
        header = f.readline()
        X = int(header.split(' X ')[1].split()[0])
        for line in f:
            p, a, b = map(int, line.split())
            s[1][p], s[2][p] = a, b
    for t in (1, 2):
        assert sorted(s[t]) == list(range(P)), 'matching is not a bijection'
    M = 5
    edges = []
    for k, pts in enumerate(L):
        for p in pts:
            for c in range(M):
                edges.append((M * p + c, M * (P + k) + c))
    for t in (1, 2):
        for p in range(P):
            if p == X:
                continue
            for c in range(M):
                edges.append((M * p + c, M * (P + s[t][p]) + (c + t) % M))
    g = 2 * P * M
    for c in range(M):
        edges += [(M * X + c, g), (M * X + c, g + 1), (M * (P + s[1][X]) + c, g + 2), (M * (P + s[2][X]) + c, g + 3)]
    edges = sorted((min(a, b), max(a, b)) for a, b in edges)
    assert len(set(edges)) == len(edges), 'repeated edge'
    n = g + 4
    deg = [0] * n
    for a, b in edges:
        deg[a] += 1; deg[b] += 1
    assert max(deg) <= 12
    h = hashlib.sha256()
    with open(out, 'w') as f:
        line = f'{n}\n'; f.write(line); h.update(line.encode())
        for a, b in edges:
            line = f'{a} {b}\n'; f.write(line); h.update(line.encode())
    dig = h.hexdigest()
    print(f'n={n} edges={len(edges)} max degree {max(deg)}; sha256 {dig}; '
          f'{"matches" if dig == EXPECTED else "DIFFERS from"} the recorded graph')


if __name__ == '__main__':
    main()
