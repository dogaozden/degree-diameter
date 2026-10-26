"""Build W(q) (q=5,7) point-line data and write plain files for the exact searches.
Writes: W{q}_lines.txt (nl lines, each line = 6 or 8 points), W{q}_col.txt (collinearity lists),
W{q}_spread.txt (regular spread line ids), W{q}_pts.txt (n) ."""
import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
import gqlib
q = int(sys.argv[1])
G = gqlib.W(q); G.check()
S = gqlib.regular_spread_W(G)
assert gqlib.is_partial_spread(G, S) and len(S) == q*q+1
with open('W%d_lines.txt' % q, 'w') as f:
    f.write('%d %d\n' % (G.np, G.nl))
    for l in G.lines: f.write(' '.join(map(str, l)) + '\n')
with open('W%d_col.txt' % q, 'w') as f:
    f.write('%d\n' % G.np)
    for p in range(G.np):
        nb = np.nonzero(G.col[p])[0]
        f.write('%d %s\n' % (len(nb), ' '.join(map(str, nb))))
with open('W%d_spread.txt' % q, 'w') as f:
    f.write('%d\n' % len(S)); f.write(' '.join(map(str, S)) + '\n')
print(G.name, G.np, G.nl, 'spread', len(S), 'ok', 'points per col', G.col.sum(1)[:3])
