"""Classify the singular-pattern sets of the (4,3) charts that cover both diagonals (one chart per mask solution,
tetra/tetra), up to relabelling the 4 letters.  Writes one representative chart per class (../k4q3_diag_cls<i>.txt)."""
import importlib.util, sys, itertools, subprocess, random, os
sys.argv = ['diag_charts.py', 'tetra', 'tetra', '300', '1', '3', '/dev/null']
src = open('diag_charts.py').read()
src = src[:src.index('charts = []')]
ns = {'__name__': 'x'}; exec(compile(src, 'diag_charts_head', 'exec'), ns)
sols, tables, lift, inv4, matmul, B = ns['sols'], ns['tables'], ns['lift'], ns['inv4'], ns['matmul'], ns['B']
sys.path.insert(0, '../..')
from chartlib import read_chart_txt
classes = {}
for idx, sol in enumerate(sols):
    iA, iB = sol[:4], sol[4:]
    As = [lift(s, tables[s][2][(tables[s][0][iA[s]], tables[s][1][iB[s]])][0], 1, [0, 0, 0]) for s in range(4)]
    G = inv4(As[0]); As = [matmul(A, G) for A in As]
    fn = '/tmp/claude-0/-home-user-degree-diameter/8e7a80fa-6b09-58cb-8199-8d05845bbe55/scratchpad/w/cls_tmp.txt'
    with open(fn, 'w') as fo:
        fo.write(''.join(' '.join(str(x) for row in A for x in row) + ' \n' for A in As))
        fo.write(''.join(' '.join(map(str, B[s])) + ' \n' for s in range(4)))
    ch = read_chart_txt(fn, 3, 4)
    sing = frozenset((s, p) for s, p, r in ch.singular_patterns())
    canon = min(tuple(sorted((s, tuple(perm[x] for x in p)) for s, p in sing)) for perm in itertools.permutations(range(4)))
    if canon not in classes:
        classes[canon] = idx
        os.system('cp %s ../k4q3_diag_cls%d.txt' % (fn, len(classes) - 1))
print('solutions', len(sols), 'singular-set classes up to letter relabelling:', len(classes))
for i, (c, idx) in enumerate(classes.items()):
    a = sum(1 for s, p in c if s == 'A'); print('class', i, 'from solution', idx, 'A-side', a, 'B-side', len(c) - a, 'patterns', [s + ''.join(map(str, p)) for s, p in c])
