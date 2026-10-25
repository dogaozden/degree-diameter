import sys, numpy as np, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/hexfam_r2/c5')
from chartlib import *
q = int(sys.argv[1]); src = sys.argv[2]
G = Geo(q)
ids = [int(t) for t in open(src).read().split()]
e4 = e4_id(G)
t0 = time.time()
M = find_iso(G, ids[0], e4)
pts, zeros = chart_of(G, M, ids)
print('q', q, 'set', len(ids), 'zeros', zeros, 'chart pts', len(pts), 'time', round(time.time() - t0, 2))
# verify: chart pts + e4 pairwise opposite in H(q) (via Q' differences) and as point ids
back = ids_of_chart(G, pts) + [e4]
print('check opp (ids, ext):', G.check_opp(back), 'size', len(set(back)))
# Q'-check on chart
Qp = lambda t: (t[2] * t[2] - t[0] * t[3] - t[1] * t[4]) % q
ok = all(((tuple((x - y) % q for x, y in zip(u, v)) and Qp(tuple((x - y) % q for x, y in zip(u, v)))) != 0) for i, u in enumerate(pts) for v in pts[i + 1:])
print('chart pairwise Q\' ok:', ok)
with open(sys.argv[3], 'w') as fh:
    fh.write(repr(pts) + '\n')
