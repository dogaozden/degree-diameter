import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/handsoff-49/w13')
from meta import meta_table
out = open('centre_1243_1300.tsv', 'w')
for line in open('meta_1243_1300.txt'):
    N, spec = line.split()
    _, m, k, r = spec.split(':'); m, k, r = int(m), int(k), int(r)
    T = meta_table(m, k, r)
    cen = int(np.sum(np.all(T == T.T, axis=1)))
    inv = int(np.sum(T[np.arange(int(N)), np.arange(int(N))] == 0)) - 1
    out.write("%s\t%s\t%d\t%d\n" % (N, spec, cen, inv))
out.close()
