import json, sys
from w3k import W3, orbits
import groups
d = json.load(open(sys.argv[1]))
W = W3(d['q']); q = W.q
M = set(d['M'])
orbs, of = orbits(len(W.pts), groups.gens(W, 'ns:1'))
cls = {}
for p in M: cls[of[p]] = cls.get(of[p], 0) + 1
print('Singer classes hit:', cls)
o5, of5 = orbits(len(W.pts), groups.gens(W, d.get('sym') or 'ns:5'))
sub = {}
for k, o in enumerate(o5):
    if o[0] in M: sub.setdefault(of[o[0]], []).append(k)
print('suborbits by class', sub)
