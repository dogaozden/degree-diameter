"""Independent check of a build_rel.py output (json): T is relaxed, slots distinct, the RELAXED-PAIR RULE holds."""
import sys, json
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
from gqlib import W, is_partial_ovoid
d = json.load(open(sys.argv[1]))
G = W(5).dual(); O = set(d['O']); T = d['T']
assert is_partial_ovoid(G, sorted(O))
partner = {}
for l in T:
    for m in T:
        if m != l and G.con[l, m]:
            assert l not in partner, 'two partners'
            z = (set(G.lines[l]) & set(G.lines[m])); assert len(z) == 1 and not (z & O), 'bad meeting point'
            partner[l] = m
def opt(p):  # ovoid point on line p
    return [x for x in G.lines[p] if x in O][0]
ok = True
def slot(hub, j):
    return next(s for s in hub if s[0] == j)
for h in d['Bhubs']:
    assert sorted(s[0] for s in h) == list(range(5))
    s2, s4 = slot(h, 2), slot(h, 4)
    if s2[1] in partner: ok &= slot(h, 3)[1] == opt(partner[s2[1]]) and slot(h, 3)[2] == [3, 4]
    if s4[1] in partner:
        tgt = 0 if s4[2] == [4, 0] else 1
        ok &= slot(h, tgt)[1] == opt(partner[s4[1]])
for g in d['Ahubs']:
    assert sorted(s[0] for s in g) == list(range(5))
    s0, s1, s3 = slot(g, 0), slot(g, 1), slot(g, 3)
    for s in (s0, s1):
        if s[1] in partner: ok &= slot(g, 4)[1] == opt(partner[s[1]])
    if s3[1] in partner: ok &= slot(g, 2)[1] == opt(partner[s3[1]])
for key in ('Bhubs', 'Ahubs'):
    allslots = [json.dumps(s) for h in d[key] for s in h]
    assert len(allslots) == len(set(allslots)), 'slot reused in ' + key
print('|T| =', len(T), 'pairs =', len(partner) // 2, 'K_B =', len(d['Bhubs']), 'K_A =', len(d['Ahubs']), 'rule holds:', bool(ok))
