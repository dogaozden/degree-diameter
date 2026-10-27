#!/usr/bin/env python3
"""No local refutation of 10-cycles at n = 248: build a configuration graph whose only cycles of length <= 12 are its
10-cycles, and check that every vertex has excess R(v) = 3 (as at n = 248) while each side has far more than 124
vertices. Configuration: a (5,3)-biregular bipartite incidence graph of girth >= 10 between N "cycles" and 5N/3
"lines", made as a Z_M voltage lift of K_{3,5} with random voltages (rejected until girth >= 10). Graph: one 10-cycle
per cycle-vertex; line l has spokes y_l, Y_l; for each incidence (l, j) a pair index r = pi_j(l) (bijection lines of j
-> {0..4}); y_l joins the even member of {r, r+5} on cycle j, Y_l the odd member.
Usage: local_r3.py M seed"""
import sys, random, networkx as nx
M, seed = int(sys.argv[1]), int(sys.argv[2]); random.seed(seed)
for attempt in range(1000):
    volt = {(a, b): random.randrange(M) for a in range(3) for b in range(5)}
    I = nx.Graph()
    for (a, b), t in volt.items():
        for g in range(M): I.add_edge(('c', a, g), ('l', b, (g + t) % M))
    if nx.girth(I) >= 10: break
else: sys.exit("no lift with girth >= 10")
cyc = sorted(n for n in I if n[0] == 'c'); lin = sorted(n for n in I if n[0] == 'l')
G = nx.Graph()
for c in cyc:
    for i in range(10): G.add_edge((c, i), (c, (i + 1) % 10))
    for l, r in zip(sorted(I[c]), random.sample(range(5), 5)):
        e, o = (r, r + 5) if r % 2 == 0 else (r + 5, r)
        G.add_edge(('y', l), (c, e)); G.add_edge(('Y', l), (c, o))
assert all(d == 3 for _, d in G.degree()) and nx.is_bipartite(G)
def R(v):
    front = [(v, None)]; tot = 1; ends = {v}
    for L in range(1, 7):
        front = [(y, x) for x, prev in front for y in G[x] if y != prev]
        if L % 2 == 0: tot += len(front); ends |= {x for x, _ in front}
    return tot - len(ends)
from collections import Counter
vals = Counter(R(v) for v in G)
print(f"M={M} cycles={len(cyc)} lines={len(lin)} n={G.number_of_nodes()} side={G.number_of_nodes() // 2} "
      f"incidence girth={nx.girth(I)} graph girth={nx.girth(G)} R histogram={dict(vals)}")
