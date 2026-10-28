"""Input for relaxed.c on W(q): vertices = points of W(q) (= lines of Q(4,q)); neighbours = collinear points;
flag 1 iff the joining W-line is in the regular spread S (= ovoid O of Q(4,q)), which is forbidden."""
import sys
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
import numpy as np
from gqlib import W, regular_spread_W
q = int(sys.argv[1]); Wq = W(q); S = set(regular_spread_W(Wq))
lid = {}
for li, l in enumerate(Wq.lines):
    for a in l:
        for b in l:
            if a != b: lid[(a, b)] = li
with open(sys.argv[2], 'w') as f:
    f.write('%d\n' % Wq.np)
    for p in range(Wq.np):
        nbs = np.nonzero(Wq.col[p])[0]
        f.write('%d ' % len(nbs) + ' '.join('%d %d' % (j, 1 if lid[(p, j)] in S else 0) for j in nbs) + '\n')
print('points', Wq.np, 'spread lines', len(S), 'degree', len(np.nonzero(Wq.col[0])[0]))
