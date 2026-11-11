"""For even-order meta groups (w2's list, orders 2486..2600): count involutions and central involutions."""
import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/handsoff-49/w13')
from meta import meta_table
out = open('central_scan.tsv', 'w')
for line in open('/home/user/degree-diameter/research/squads/handsoff-49/w2/groups_all.txt'):
    N, m, k, r = map(int, line.split())
    if N % 2: continue
    T = meta_table(m, k, r)
    idx = np.arange(N)
    inv = np.nonzero(T[idx, idx] == 0)[0]; inv = inv[inv != 0]
    cen = [int(x) for x in inv if np.array_equal(T[x], T[:, x])]
    out.write("%d\t%d\t%d\t%d\t%d\t%d\t%s\n" % (N, m, k, r, len(inv), len(cen), ",".join(map(str, cen))))
out.close()
