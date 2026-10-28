"""Writes the collinearity graph of W(q) for the relaxed-set searches of d5relax/ (job d5-relax).
Points of W(q) are the lines of Q(4,q) = gqlib.W(q).dual(), so a relaxed set of points of W(q) is a relaxed freed set
of lines on the D->H arcs of D5_QUADRANGLE.md, section 7.  Files (in data/):
  W<q>_adj.txt    n, then per point: degree and the collinear points
  W<q>_lines.txt  number of lines, then per line its q+1 points
  W<q>_spread.txt per point the index (0..q^2) of the line of the regular spread of Lemma 1.1 through it
usage: python3 export_w.py q"""
import sys, os
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'd5gq'))
from gqlib import W, regular_spread_W
q = int(sys.argv[1]); G = W(q); S = regular_spread_W(G)
os.makedirs(os.path.join(HERE, 'data'), exist_ok=True)
pre = os.path.join(HERE, 'data', 'W%d' % q)
with open(pre + '_adj.txt', 'w') as f:
    f.write('%d\n' % G.np)
    for p in range(G.np):
        nb = np.nonzero(G.col[p])[0]
        f.write('%d %s\n' % (len(nb), ' '.join(map(str, nb))))
with open(pre + '_lines.txt', 'w') as f:
    f.write('%d\n' % G.nl)
    for l in G.lines:
        f.write(' '.join(map(str, l)) + '\n')
sp = [-1] * G.np
for i, l in enumerate(S):
    for p in G.lines[l]:
        assert sp[p] < 0; sp[p] = i
assert min(sp) >= 0
with open(pre + '_spread.txt', 'w') as f:
    f.write(' '.join(map(str, sp)) + '\n')
print('W(%d): %d points, %d lines, collinearity degree %d' % (q, G.np, G.nl, int(G.col[0].sum())))
