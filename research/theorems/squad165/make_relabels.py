#!/usr/bin/env python3
"""For a chart (chart_search.c text format), write the 24 colour relabellings as pattern tables and as charts.
Relabelling q (permutation p): controller colour c uses chart letter p[c].  Pattern file OUT_qXX.txt has, for
the pattern (i1,i2,i3,i4), the rank of the chart's pattern (p[i1],...,p[i4]); chart file OUT_chart_qXX.txt is the
relabelled chart A'_c = A_{p[c]} A_{p[0]}^-1, b'_c = b_{p[c]} (gauge A'_0 = I; same lift up to isomorphism), to be
used with controllers whose colours are NOT relabelled.  Permutation list: OUT_perms.txt.
usage: python3 make_relabels.py CHART OUT"""
import sys, itertools
from lift_check import load_chart, rank
from chart import mat_vec, mat_inv, mat_mul
A, b = load_chart(sys.argv[1]); Ai = [mat_inv(M) for M in A]; out = sys.argv[2]
r = {}
for (i1, i2, i3, i4) in itertools.product(range(4), repeat=4):
    if i1 == i2 or i2 == i3 or i3 == i4: continue
    r[('A', i1, i2, i3, i4)] = rank([mat_vec(Ai[i2], b[i1]), mat_vec(Ai[i2], b[i2]), mat_vec(Ai[i3], b[i3]), mat_vec(Ai[i3], b[i4])])
    r[('B', i1, i2, i3, i4)] = rank([mat_vec(A[i2], mat_vec(Ai[i1], b[i1])), b[i2], b[i3], mat_vec(A[i3], mat_vec(Ai[i4], b[i4]))])
with open(out + '_perms.txt', 'w') as g:
    for K, p in enumerate(itertools.permutations(range(4))):
        g.write("q%02d %s\n" % (K, p))
        with open(out + '_q%02d.txt' % K, 'w') as f:
            for s in 'AB':
                for q in itertools.product(range(4), repeat=4):
                    if q[0] == q[1] or q[1] == q[2] or q[2] == q[3]: continue
                    f.write("%s %d %d %d %d %d\n" % ((s,) + q + (r[(s, p[q[0]], p[q[1]], p[q[2]], p[q[3]])],)))
        G = mat_inv(A[p[0]])
        with open(out + '_chart_q%02d.txt' % K, 'w') as f:
            for c in range(4):
                M = mat_mul(A[p[c]], G); f.write(' '.join(str(M[i][j]) for i in range(4) for j in range(4)) + '\n')
            for c in range(4): f.write(' '.join(map(str, b[p[c]])) + '\n')
print('wrote 24 pattern files and 24 charts with prefix', out)
