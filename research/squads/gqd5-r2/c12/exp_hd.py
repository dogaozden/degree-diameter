"""c12 experiment: freed point set T on every H->D arc (identity), partial spread on D->H, c = 0; hubs with the
index-order slot assignment and NO hub graph.  Reports far pairs split into level-level, hub-level, hub-hub."""
import sys, time; sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r2/c12')
from hdlib import *
from reach import far_pairs
import numpy as np, json
q = int(sys.argv[1]); mode = sys.argv[2]
types = 'HHHDHHD'; arcs = rotational_arcs(7)
Wq, G, ovoid = setup(q)
ps = greedy_partial_spread(G)
if mode == 'ovoid':
    T = ovoid
elif mode.startswith('file:'):
    T = json.load(open(mode[5:]))
n, E, KB, KA = make(q, types, arcs, T, ps)
N_lev = 7 * (G.np + G.nl)
far = far_pairs(n, E)
lev = np.arange(N_lev); hub = np.arange(N_lev, n)
ll = far[np.ix_(lev, lev)].sum() // 2
hl = far[np.ix_(hub, lev)].sum()
hh = far[np.ix_(hub, hub)].sum() // 2
print('q=%d |T|=%d KB=%d KA=%d n=%d far level-level=%d hub-level=%d hub-hub=%d' % (q, len(T), KB, KA, n, ll, hl, hh))
