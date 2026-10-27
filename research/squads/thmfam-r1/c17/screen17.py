import sys, itertools, json
sys.path.insert(0, '/home/user/degree-diameter/research/squads/thmfam-r1/c17')
from common17 import *
# SL(2,Z) with entries in [-2,2]
mats = [M for M in itertools.product(range(-2, 3), repeat=4) if M[0]*M[3]-M[1]*M[2] == 1]
orbs = {}
for M in mats:
    key = frozenset(orbit(M))
    orbs.setdefault(key, M)
reps = list(orbs.values())
# identify orbits that differ only by sign
def neg(M): return tuple(-x for x in M)
pairs = []
seen = set()
for i, X in enumerate(reps):
    for Y in reps[i+1:]:
        if frozenset(orbit(X)) & frozenset(orbit(Y)): continue
        if any(neg(Mx) in frozenset(orbit(Y)) for Mx in orbit(X)): continue
        pairs.append((X, Y))
print('orbit reps', len(reps), 'pairs', len(pairs), flush=True)
res = []
for X, Y in pairs:
    tot = []
    ok = True
    for q in (29, 41):
        lines = [('%d %d %d %d 0' % tuple(x % q for x in M)) for M in orbit(X) + orbit(Y)]
        e = excess_of(q, 1, lines)
        if e is None: ok = False; break
        tot.append(e['excess'])
    if ok: res.append((sum(tot)/len(tot), X, Y, tot))
res.sort()
for r in res[:12]: print(json.dumps({'mean': round(r[0],3), 'X': r[1], 'Y': r[2], 'ex': [round(t,3) for t in r[3]]}))
json.dump([[r[1], r[2], r[0]] for r in res[:12]], open('/home/user/degree-diameter/research/squads/thmfam-r1/c17/screen_top.json', 'w'))
