# Writes the relaxed.c input for W(5): vertices = points of W(5) (= lines of Q(4,5)); neighbours = W-collinear points;
# flag 1 iff the joining W-line is in the regular spread (= ovoid O of Q(4,5)), which is forbidden.
import sys
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
from gqlib import W, regular_spread_W
Wq = W(5)
S = set(regular_spread_W(Wq))
nb = {p: [] for p in range(Wq.np)}
for li, l in enumerate(Wq.lines):
    for a in l:
        for b in l:
            if a != b:
                nb[a].append((b, 1 if li in S else 0))
with open(sys.argv[1], 'w') as f:
    f.write('%d\n' % Wq.np)
    for p in range(Wq.np):
        f.write('%d ' % len(nb[p]) + ' '.join('%d %d' % x for x in nb[p]) + '\n')
print('points', Wq.np, 'spread', len(S), 'deg', len(nb[0]))
