"""Collinearity graph of Q(4,q) (= concurrency graph of the lines of W(q)) from data/W<q>_lines.txt, for relaxed
POINT sets of Q(4,q) (the dual of section 7, freed sets on H->D arcs).  Point i of Q(4,q) = line i of W(q), as in
gqlib's W(q).dual().  usage: python3 export_q4.py q   (writes data/Q<q>_adj.txt)"""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
q = int(sys.argv[1]); pre = os.path.join(HERE, 'data')
L = [list(map(int, s.split())) for s in open(os.path.join(pre, 'W%d_lines.txt' % q)).read().strip().split('\n')[1:]]
n = len(L); through = {}
for i, l in enumerate(L):
    for p in l: through.setdefault(p, []).append(i)
with open(os.path.join(pre, 'Q%d_adj.txt' % q), 'w') as f:
    f.write('%d\n' % n)
    for i, l in enumerate(L):
        nb = sorted({j for p in l for j in through[p] if j != i})
        f.write('%d %s\n' % (len(nb), ' '.join(map(str, nb))))
print('Q(4,%d): %d points' % (q, n))
