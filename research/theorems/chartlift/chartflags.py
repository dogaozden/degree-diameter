"""Write the chart-flags file read by ctrl_search.c: singular NB patterns, pencil completeness, diagonal coverage.
usage: python3 chartflags.py CHART.txt q k out.flags"""
import sys, itertools
from chartlib import read_chart_txt
ch = read_chart_txt(sys.argv[1], int(sys.argv[2]), int(sys.argv[3])); k = ch.k
sing = {(s, p) for s, p, r in ch.singular_patterns()}
with open(sys.argv[4], 'w') as f:
    f.write('%d\n' % k)
    for s in 'AB':
        f.write(' '.join(str(int((s, p) in sing)) for p in itertools.product(range(k), repeat=4)) + '\n')
    for s in 'AB':
        f.write(' '.join(str(int(i != j and ch.pencil(s, i, j)[1])) for i in range(k) for j in range(k)) + '\n')
    f.write('%d %d\n' % (int(ch.diagonal('A')[1]), int(ch.diagonal('B')[1])))
print('singular', len(sing), 'pencil fails', len(ch.pencil_report()), 'diag', ch.diagonal('A')[1], ch.diagonal('B')[1])
