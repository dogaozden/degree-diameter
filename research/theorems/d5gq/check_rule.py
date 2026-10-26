"""Checks the hypotheses of Proposition 7.2 for a solution file: T is a relaxed set (every line meets at most one other,
meeting point off the ovoid), and for every partnered line l on every D->H arc the A-hub at the B-slot (l, arc) sits, in
the source D-level, at a point of the partner m.  usage: python3 check_rule.py SOLUTION.json"""
import sys, json
from gqlib import W
from build_relaxed import partners
d = json.load(open(sys.argv[1]))
G = W(d['q']).dual(); PT = partners(G, d['T'], d['ovoid_Q4'])
Ah = d['Ahub_slots']; ok = bad = 0
for (u, v) in d['arcs']:
    if d['types'][u] == 'D' and d['types'][v] == 'H':
        for l, (m, om) in PT.items():
            gs = [g for g in Ah if g[v][1] == l and tuple(g[v][2]) == (u, v)]
            if gs and gs[0][u][1] in G.lines[m]: ok += 1
            else: bad += 1
print('relaxed set of %d lines, %d partnered; A-hub rule satisfied %d, violated %d' % (len(d['T']), len(PT), ok, bad))
