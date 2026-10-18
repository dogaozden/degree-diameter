"""Take a diameter-4 record graph apart as a GQ copy graph (Theorem B of research/NOTE.md, stand-ins allowed).

Copy pairs = same-side vertices with >= 3 common neighbours (a copy shares its q+1 base neighbours with its original).
The side with fewer pairs holds the line copies. A line copy should be adjacent to one stand-in per point of its line;
any further edges are stripped and the stripped graph is re-checked with lib.is_valid. Also counts the points whose
original and copy each serve a different line copy (stand-ins essential there).

Usage: python3 copy_structure.py GRAPH.json q 1 DELTA     (2026-10-18: 359 island graph -> 21 extra edges, 5 stand-in
points; q4_share_q5_n359 -> 0 extra, 4; 1774 island graph -> 1 extra, 1; gq4_q11_n3122 -> 0 extra, 0)
"""
import json, sys, collections
sys.path.insert(0, '/Users/dogaozden/AI_Projects/degree-diameter')
from problems.bipartite_dd import lib
f, q, D = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
n, E = json.load(open(f))['output']
adj = [set() for _ in range(n)]
for u, v in E: adj[u].add(v); adj[v].add(u)
col = [-1]*n; col[0] = 0; st = [0]
while st:
    x = st.pop()
    for y in adj[x]:
        if col[y] < 0: col[y] = 1-col[x]; st.append(y)
cnt = collections.Counter()
for v in range(n):
    for u in adj[v]:
        for w in adj[u]:
            if w > v: cnt[(v, w)] += 1
P = [k for k, c in cnt.items() if c >= 3]
side_pairs = collections.Counter(col[a] for a, b in P)
lside = min(side_pairs, key=side_pairs.get)
mate = {}
for a, b in P: mate[a] = b; mate[b] = a
under = lambda x: min(x, mate.get(x, x))          # underlying vertex id of a point (cluster rep)
extra = []
stand_in_points = set()
for a, b in P:
    if col[a] != lside: continue
    B = adj[a] & adj[b]
    def full(m):  # adjacent to both members of every point cluster meeting B
        return all(mate[x] in adj[m] for x in B if x in mate)
    fa, fb = full(a), full(b)
    assert fa or fb, 'no original line in pair'
    org, cp = (a, b) if fa else (b, a)
    under_B = {under(x) for x in B}
    under_org = {under(x) for x in adj[org]}
    assert len(B) == q + 1 and len(under_B) == q + 1 and under_B == under_org, 'shared set is not one stand-in per point'
    extra += [(cp, x) for x in adj[cp] - B]
    stand_in_points |= {x for x in B if x in mate and x > mate[x]}   # served by the non-rep member
ex = {frozenset(e) for e in extra}
E2 = [e for e in E if frozenset(e) not in ex]
print(f, f'line-copy side {lside}; extra edges on line copies: {len(extra)}; stripped graph valid (deg {q+2 if D else 0}):',
      lib.is_valid(n, E2, int(sys.argv[4]), 4))
# stand-ins essential: point clusters where both members serve some line copy
lc = {cp for a, b in P if col[a] == lside for cp in (a, b)}
both = 0
for a, b in P:
    if col[a] == lside: continue
    sa = [y for y in adj[a] - adj[b] if col[y] == lside and y in lc]
    sb = [y for y in adj[b] - adj[a] if col[y] == lside and y in lc]
    if sa and sb: both += 1
print('  point clusters where original and copy each serve a different line copy (stand-ins essential):', both)
