#!/usr/bin/env python3
"""lcf2edges.py LCFFILE ORDER INDEX OUT: build the cubic graph '! ORDER INDEX: [a_0,...,a_{k-1}]^m' (Foster census
LCF notation: Hamiltonian cycle 0-1-...-(n-1)-0 plus chords i ~ i + a_(i mod k) mod n) and write an edge list
(first line n, then "u v"). Checks: n = k m, every vertex has degree 3, the chord map is an involution, no loops or
multi-edges. Prints n, number of edges and whether the graph is bipartite (BFS 2-colouring)."""
import re, sys
from collections import deque
fn, order, index, out = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
line = next(l for l in open(fn) if re.match(rf"^! {order} {index}:", l))
m = re.search(r"\[([-0-9,\s]+)\]\^(\d+)", line)
a = [int(x) for x in m.group(1).split(",")]; rep = int(m.group(2)); n = len(a) * rep
assert n == order, (n, order)
E = set()
for i in range(n):
    E.add((min(i, (i + 1) % n), max(i, (i + 1) % n)))
    j = (i + a[i % len(a)]) % n
    assert j != i
    jj = (j + a[j % len(a)]) % n
    assert jj == i, "chord map is not an involution"
    E.add((min(i, j), max(i, j)))
adj = [[] for _ in range(n)]
for u, v in E: adj[u].append(v); adj[v].append(u)
assert all(len(x) == 3 for x in adj), "not cubic"
col = [-1] * n; col[0] = 0; q = deque([0]); bip = True
while q:
    u = q.popleft()
    for v in adj[u]:
        if col[v] < 0: col[v] = 1 - col[u]; q.append(v)
        elif col[v] == col[u]: bip = False
with open(out, "w") as f:
    f.write(f"{n}\n")
    for u, v in sorted(E): f.write(f"{u} {v}\n")
print(f"n={n} edges={len(E)} cubic=yes bipartite={'yes' if bip else 'no'}")
