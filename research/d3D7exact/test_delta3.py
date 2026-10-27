#!/usr/bin/env python3
"""Test the delta = 3 structure theorem (cell notes section 2.6) on real graphs, for any odd D: a cubic bipartite graph
of diameter D with m = 2^D - 4 per side. Short cycles: s = 2D - 4 (10 for D = 7) and l = 2D - 2 (12 for D = 7).
Checks: girth >= s; R(v) = 3; every vertex on <= 1 s-cycle; s-cycle vertices on no l-cycle; spokes are type S;
a(v) in {0,1,3} with l-cycle counts 0 / 2 / 3-or-4 for a = 3 / 1 / 0; Rep(y) = N(y') for spoke pairs; a(y) = a(y').
Usage: test_delta3.py EDGES D"""
import sys, itertools
from collections import Counter
f = open(sys.argv[1]); n = int(f.readline()); D = int(sys.argv[2])
adj = {i: [] for i in range(n)}
for line in f:
    a, b = map(int, line.split()); adj[a].append(b); adj[b].append(a)
L = D - 1; s, l = 2 * D - 4, 2 * D - 2
def nb_walks(v, maxlen):
    out = []; st = [(v, None, 0, (v,))]
    while st:
        x, prev, d, path = st.pop()
        out.append(path)
        if d < maxlen:
            for y in adj[x]:
                if y != prev: st.append((y, x, d + 1, path + (y,)))
    return out
def cycles_through(v, length):  # simple cycles through v of given length, as frozensets of edges
    res = set()
    for path in nb_walks(v, length - 1):
        if len(path) == length and v in adj[path[-1]] and len(set(path)) == length:
            res.add(frozenset(frozenset(e) for e in zip(path, path[1:] + (v,))))
    return res
fails = Counter(); stats = Counter()
R = {}; Rep = {}
for v in range(n):
    ends = Counter(p[-1] for p in nb_walks(v, L) if (len(p) - 1) % 2 == 0)
    R[v] = sum(ends.values()) - len(ends); Rep[v] = Counter({x: c - 1 for x, c in ends.items() if c > 1})
    if R[v] != 3: fails['R!=3'] += 1
cs = {v: cycles_through(v, s) for v in range(n)}; cl = {v: cycles_through(v, l) for v in range(n)}
girth_ok = all(not cycles_through(v, g) for v in range(n) for g in range(4, s, 2))
if not girth_ok: fails['girth<s'] += 1
T = {v for v in range(n) if cs[v]}
for v in T:
    if len(cs[v]) > 1: fails['T on >1 s-cycle'] += 1
    if cl[v]: fails['T on l-cycle'] += 1
spoke = {}
for v in T:
    C = next(iter(cs[v])); cv = {x for e in C for x in e}
    sp = [y for y in adj[v] if y not in cv]
    if len(sp) != 1: fails['spoke count'] += 1; continue
    spoke[v] = sp[0]
    if sp[0] in T: fails['spoke in T'] += 1
a = {v: sum(1 for y in adj[v] if y in T) for v in range(n) if v not in T}
for v, av in a.items():
    stats[f'a={av}, l-cycles={len(cl[v])}'] += 1
    if av == 2: fails['a=2'] += 1
    exp = {3: {0}, 1: {2}, 0: {3, 4}}.get(av, set())
    if len(cl[v]) not in exp: fails[f'a={av} with {len(cl[v])} l-cycles'] += 1
for v in T:  # spoke pairs: v and its antipode on its s-cycle
    C = next(iter(cs[v])); cyc = [v]; prev = None
    cv = {x for e in C for x in e}
    while len(cyc) < s:
        nxt = [y for y in adj[cyc[-1]] if y in cv and y != prev and frozenset((cyc[-1], y)) in C][0]
        prev = cyc[-1]; cyc.append(nxt)
    ant = cyc[s // 2]; y, y2 = spoke[v], spoke[ant]
    if set(Rep[y].elements()) != set(adj[y2]) or sum(Rep[y].values()) != 3: fails['Rep(y) != N(y\')'] += 1
    if a[y] != a[y2]: fails["a(y) != a(y')"] += 1
print(f"n={n} D={D} |T|={len(T)} s-cycles={len(set().union(*cs.values()))} l-cycles={len(set().union(*cl.values()))}")
print("stats:", dict(stats)); print("failures:", dict(fails) if fails else "none")
