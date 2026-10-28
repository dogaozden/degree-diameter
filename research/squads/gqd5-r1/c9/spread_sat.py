import sys, time; sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r1/c9')
from lab import G
from indep import indep_sat
import numpy as np
k = int(sys.argv[1]); t = time.time()
S = indep_sat(G.con, k, forced_in=[3])
print('k', k, 'found' if S else 'none', '%.0fs' % (time.time() - t), S, flush=True)
if S: np.save('spread_sat_%d.npy' % k, np.array(S))
