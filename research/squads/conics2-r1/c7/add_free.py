import sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/conics2-r1/c7')
from common import *
q = int(sys.argv[1])
q, N, LP, PL, X, G, spread_pts, spread_lines, v = setup(q)
inG = np.zeros(N, bool); inG[G] = True
cnt = inG[PL].sum(1)
sl = [int(l) for l in spread_lines if l != v]
free = [l for l in sl if (cnt[LP[l]] == 0).all()]
G2 = np.unique(np.concatenate([G, np.array(free, dtype=np.int64)]))
np.savetxt(f'/home/user/degree-diameter/research/squads/conics2-r1/c7/G_free_q{q}.txt', G2, fmt='%d', newline=' ')
print('q', q, 'free spread lines', len(free), 'size', len(G2), 'valid', valid(LP, PL, N, G2))
