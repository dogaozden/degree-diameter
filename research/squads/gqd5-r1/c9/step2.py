import sys, time; sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r1/c9')
from lab import *
from indep import indep_sat, max_indep
t=time.time()
S = max_indep(G.con, 15, 24)
print('max partial spread of Q(4,5) found:', len(S), 'in %.1fs' % (time.time()-t))
print(sorted(S))
O = max_indep(G.col, 20, 30)
print('max partial ovoid of Q(4,5) found:', len(O))
np.save('/home/user/degree-diameter/research/squads/gqd5-r1/c9/spread21.npy', np.array(S))
np.save('/home/user/degree-diameter/research/squads/gqd5-r1/c9/ovoid26.npy', np.array(O))
