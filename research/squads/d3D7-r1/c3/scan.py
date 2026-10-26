import sys, random, collections, itertools, json
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d3D7-r1/c3')
from gadget import *
n0, E0 = load('/home/user/degree-diameter/research/d3D7/seeds/conder168.edges')
n0, E0 = relabel(n0, E0)
S = set(E0)
res = []
for e1, e2 in itertools.combinations(E0, 2):
    a1, b1 = e1; a2, b2 = e2
    if len({a1, a2, b1, b2}) < 4: continue
    if (a1, b2) in S or (a2, b1) in S: continue
    d = dist_between(n0, E0, [a1, b1], [a2, b2])
    n2, E2 = gadget(n0, E0, a1, b1, a2, b2)
    c = cost(n2, E2)
    res.append((c, d, e1, e2))
print('pairs', len(res))
bydist = collections.defaultdict(list)
for r in res: bydist[r[1]].append(r[0])
for d in sorted(bydist):
    v = sorted(bydist[d])
    print('dist', d, 'count', len(v), 'min', v[0], 'median', v[len(v)//2])
res.sort()
print('best 20:')
for r in res[:20]: print(r)
json.dump(res, open('/home/user/degree-diameter/research/squads/d3D7-r1/c3/scan170.json', 'w'))
