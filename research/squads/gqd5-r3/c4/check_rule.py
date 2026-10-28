"""Independent check of a build.py json: T relaxed, slots distinct, A-hub rule of Proposition 7.2 (which partnered
lines satisfy it).  usage: python3 check_rule.py out.json"""
import sys, json
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
from gqlib import W, Q4
d = json.load(open(sys.argv[1]))
G = Q4(d['q']); O = set(d['O']); T = d['T']
P = {}
for l in T:
    ms = [m for m in T if m != l and G.con[l, m]]
    assert len(ms) <= 1
    if ms: P[l] = ms[0]
def om(m): return [p for p in G.lines[m] if p in O][0]
hub_of = {}
for g in d['Ahubs']:
    for s in g: hub_of[(s[0], json.dumps(s[2]), s[1])] = g
# slot keys: (level, element, arc) ; the A-hub holding (l, arc) on its target level
bad = []
for l, m in P.items():
    for arc, lev_of_hub in (([4, 0], 0), ([4, 1], 1), ([2, 3], 3)):
        # the A-hub that holds the B-slot of l on the target level of arc
        hs = [g for g in d['Ahubs'] if any(s[0] == lev_of_hub and s[1] == l and s[2] == arc for s in g)]
        assert len(hs) == 1
        dlev = arc[0]
        slot = [s for s in hs[0] if s[0] == dlev][0]
        if slot[1] not in G.lines[m]: bad.append((l, arc, slot))
allslots = [json.dumps(s) for h in d['Bhubs'] + d['Ahubs'] for s in h]
print('|T| =', len(T), 'pairs =', len(P) // 2, 'K_B =', len(d['Bhubs']), 'K_A =', len(d['Ahubs']),
      'slots distinct:', len(allslots) == len(set(allslots)))
print('rule violations (line, arc, slot):', bad if bad else 'none')
