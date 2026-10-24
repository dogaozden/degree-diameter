#!/usr/bin/env python3
"""Independent graph-level check of a controller edge list ("a b" lines, A-vertex a, B-vertex b, 4-regular bipartite).
Counts the ordered same-side pairs (u, v), u = v included, with NO nonbacktracking walk of length exactly 4 from u to v
(the exact-NB-4 defect, summed over all 2m vertices).  Same definition as cost_all in research/theorems/squad165/ctrl_anneal.c.
usage: python3 check_ctrl.py controller.edges"""
import sys
edges = [tuple(map(int, l.split()[:2])) for l in open(sys.argv[1]) if l.strip()]
m = max(a for a, b in edges) + 1
assert len(edges) == 4 * m, (len(edges), m)
adj = [[] for _ in range(2 * m)]
for a, b in edges:
    adj[a].append(m + b); adj[m + b].append(a)
assert all(len(x) == 4 for x in adj), 'not 4-regular'
assert all(len(set(x)) == 4 for x in adj), 'not simple'
cost = 0
for u in range(2 * m):
    hit = set()
    for x1 in adj[u]:
        for x2 in adj[x1]:
            if x2 == u: continue
            for x3 in adj[x2]:
                if x3 == x1: continue
                for x4 in adj[x3]:
                    if x4 == x2: continue
                    hit.add(x4)
    lo = 0 if u < m else m
    cost += sum(1 for w in range(lo, lo + m) if w not in hit)
print(f'm={m} full_nb4_defect={cost}')
