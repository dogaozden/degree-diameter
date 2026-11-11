import sys, time
from hexlib import *
for q in map(int, sys.argv[1:]):
    t = time.time(); H = Hexagon(q); adj = H.incidence_adj()
    # distance profile from a few vertices: 1, q+1, (q+1)q, ..., q^5 and girth 12 (no vertex has two shortest paths at distance < 6)
    import random
    for s in random.sample(range(2 * H.N), 6):
        d = dist_array(adj, s)
        prof = [int((d == i).sum()) for i in range(8)]
        exp = [1] + [(q + 1) * q**(i - 1) for i in range(1, 6)] + [q**5, 0]
        assert prof == exp, (prof, exp)
    print('q=%d: %d points, %d lines, q+1 per line/point; distance profile from 6 random elements = 1,(q+1),...,(q+1)q^4,q^5  (%.1fs)' % (q, H.N, len(H.lines), time.time() - t))
