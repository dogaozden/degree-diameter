#!/usr/bin/env python3
"""Independent exact-NB-4 check of a bipartite controller given as an edge list "a b" (a = A-vertex, b = B-vertex,
both 0-based, every vertex of degree 4, no multi-edges).  Enumerates every nonbacktracking walk of length exactly 4
(consecutive edges distinct) from every vertex and counts the same-side ordered pairs (u, v), u = v included, that no
such walk joins.  Prints the number of uncovered pairs (0 = exact-NB-4 controller).
usage: python3 check_nb4.py controller.edges"""
import sys
from collections import defaultdict


def main():
    raw = [tuple(map(int, l.split()[:2])) for l in open(sys.argv[1]) if l.strip()]
    m = max(a for a, b in raw) + 1
    assert len(set(raw)) == len(raw), 'multi-edge in controller'
    adj = defaultdict(list)                       # vertex: A-vertex a -> a, B-vertex b -> m + b
    for eid, (a, b) in enumerate(raw):
        adj[a].append((m + b, eid))
        adj[m + b].append((a, eid))
    assert all(len(adj[v]) == 4 for v in range(2 * m)), 'not 4-regular'
    uncovered = 0
    for u in range(2 * m):
        hit = [False] * (2 * m)
        for x1, e1 in adj[u]:
            for x2, e2 in adj[x1]:
                if e2 == e1:
                    continue
                for x3, e3 in adj[x2]:
                    if e3 == e2:
                        continue
                    for x4, e4 in adj[x3]:
                        if e4 != e3:
                            hit[x4] = True
        lo, hi = (0, m) if u < m else (m, 2 * m)
        uncovered += sum(1 for v in range(lo, hi) if not hit[v])
    print(f'm={m} uncovered_same_side_pairs={uncovered}')


if __name__ == '__main__':
    main()
