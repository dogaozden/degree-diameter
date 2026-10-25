import sys, time
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D7-r4/c5')
from hexio import *
path = '/home/user/degree-diameter/research/d10D7/hex/hex_q7.bin'
t0 = time.time()
q, N, lines, coords = load_hex(path)
print('q', q, 'N', N, 'L', lines.shape[0], 'load', round(time.time() - t0, 2))
Qv = np.array([qform(coords[i], q) for i in range(N)])
print('points on Q(6,q):', int((Qv == 0).sum()), 'of', N)
pl = point_lines(q, N, lines)
# lines: pairwise perpendicular points?
bad = 0
for l in range(0, lines.shape[0], 37):
    pts = lines[l]
    for i in range(len(pts)):
        for j in range(i + 1, len(pts)):
            if bform(coords[pts[i]], coords[pts[j]], q) != 0:
                bad += 1
print('line pairs non-perp (sampled):', bad)
# opposition vs non-perp
for src in [0, 1234, 9999, 19607]:
    dp, dl = bfs_dist(q, N, lines, pl, src)
    opp_bfs = set(np.nonzero(dp == 6)[0].tolist())
    B = np.array([bform(coords[src], coords[y], q) for y in range(N)])
    nonperp = set(np.nonzero(B != 0)[0].tolist())
    from collections import Counter
    print('src', src, 'dist hist', sorted(Counter(dp.tolist()).items()), 'opp(BFS)=', len(opp_bfs), 'nonperp=', len(nonperp), 'equal', opp_bfs == nonperp, 'unreached', int((dp < 0).sum()))
