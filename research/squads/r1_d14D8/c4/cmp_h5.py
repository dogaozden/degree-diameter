import json, sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d14D8_work')
from hexlib import load
q = 5
N, LP, PL, coord = load(q)
hx = set(frozenset(tuple(int(c) for c in coord[p]) for p in LP[l]) for l in range(len(LP)))
d = json.load(open('/home/user/degree-diameter/research/gh6/hex/hexagon_q5.json'))
import itertools
P = []
for v in itertools.product(range(q), repeat=7):
    if next((c for c in v if c), 0) != 1: continue
    if (v[0] * v[4] + v[1] * v[5] + v[2] * v[6] - v[3] * v[3]) % q: continue
    P.append(v)
gh = set(frozenset(P[p] for p in l) for l in d['lines'])
print('hexgen lines', len(hx), 'gh6 lines', len(gh), 'common', len(hx & gh))
print('hexgen point0 coord', coord[0].tolist(), 'LP[0]', LP[0].tolist())
print('sample hexgen line', sorted(tuple(int(c) for c in coord[p]) for p in LP[0])[:3])
