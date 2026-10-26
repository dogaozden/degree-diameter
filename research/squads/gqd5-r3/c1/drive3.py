# Card r3c1: for cyclic and small 2-generated subgroups K of H1, orbits of K, relaxed orbits, exact max-weight union.
import sys, json, time, random, collections
sys.argv = ['x', 'H1.npy']
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r3/c1')
import numpy as np
import orbsat2 as O
H = O.H; n = O.n
idp = np.arange(n)
def closure(gens, cap=3300):
    el = {idp.tobytes(): idp}
    frontier = [idp]
    while frontier:
        nxt = []
        for x in frontier:
            for g in gens:
                y = g[x]
                k = y.tobytes()
                if k not in el:
                    el[k] = y; nxt.append(y)
                    if len(el) > cap: return None
        frontier = nxt
    return list(el.values())
# cyclic subgroups
seen = set(); cyc = []
for g in H:
    els = closure([g])
    key = frozenset(e.tobytes() for e in els)
    if key in seen: continue
    seen.add(key); cyc.append((len(els), g))
print('distinct cyclic subgroups', len(cyc), collections.Counter(o for o, _ in cyc), flush=True)
best = 0; bestT = None
results = []
def run(name, gens):
    global best, bestT
    orbs = O.orbits_of(gens)
    rel = [o for o in orbs if O.relaxed(o)]
    if not rel: return 0
    t0 = time.time()
    val, T = O.solve(orbs, 0)
    results.append((name, len(orbs), len(rel), val))
    print(name, 'orbits', len(orbs), 'relaxed', len(rel), 'best', val, 'time %.1f' % (time.time()-t0), flush=True)
    if val > best:
        best, bestT = val, T
        json.dump(sorted(int(x) for x in T), open('/home/user/degree-diameter/research/squads/gqd5-r3/c1/best_orb.json', 'w'))
    return val
for i, (o, g) in enumerate(sorted([c for c in cyc if c[0] >= int(sys.argv[-1] if sys.argv[-1].isdigit() else 5)], key=lambda t: -t[0])):
    run('cyc%d_%d' % (i, o), [g])
print('BEST after cyclic', best, flush=True)
