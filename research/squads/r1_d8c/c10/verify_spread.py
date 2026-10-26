import sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d10D8_work')
import numpy as np
from hexlib import load
q = 5
N, LP, PL, coord = load(q)
S = np.load('spread_lines.npy')
def bfs_from_line(a):
    # incidence graph distances; node ids: points 0..N-1, lines N..2N-1
    dist = np.full(2 * N, 99, dtype=np.int32)
    dist[N + a] = 0
    front = [N + a]
    d = 0
    while front:
        d += 1
        nxt = []
        for x in front:
            if x < N:
                for l in PL[x]:
                    if dist[N + l] == 99:
                        dist[N + l] = d; nxt.append(N + l)
            else:
                for p in LP[x - N]:
                    if dist[p] == 99:
                        dist[p] = d; nxt.append(p)
        front = nxt
    return dist
ok_opp = True
cover = np.zeros(N, dtype=int)
for a in S:
    dist = bfs_from_line(a)
    others = [b for b in S if b != a]
    if any(dist[N + b] != 6 for b in others):
        ok_opp = False
    cover[LP[a]] += 1
print('pairwise opposite (line-line distance 6):', ok_opp)
# coverage: points on spread lines once; others at point-distance 3 from exactly one spread line
dists_pt_to_S = np.zeros(N, dtype=int)
cnt3 = np.zeros(N, dtype=int)
for a in S:
    dist = bfs_from_line(a)
    cnt3 += (dist[:N] == 3)
print('points on spread line:', int((cover == 1).sum()), 'all covered once:', bool(((cover == 1) | (cnt3 == 1)).all()), 'ones with cover+cnt3 issue:', int(((cover == 0) & (cnt3 != 1)).sum()))
import collections
tot = collections.Counter()
for a in S:
    pass
# histogram of count of spread lines at point-distance 3 for uncovered points
h3 = collections.Counter(); h5 = collections.Counter()
c3 = np.zeros(N, int); c5 = np.zeros(N, int)
for a in S:
    dist = bfs_from_line(a)
    c3 += (dist[:N] == 3); c5 += (dist[:N] == 5)
unc = cover == 0
print('uncovered', int(unc.sum()), 'c3 hist', collections.Counter(c3[unc].tolist()), 'c5 hist', collections.Counter(c5[unc].tolist()))
