# allow_S2 for the new P sets: lines meeting P0 u P1 u R' (as in shared/mkmasks2.py)
import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/c157b-r2/shared')
import gperm
N = gperm.N; LP = gperm.LP
ld = lambda f: np.loadtxt(f, dtype=np.int64).reshape(-1)
Rp = ld('/home/user/degree-diameter/research/squads/c157b-r1/shared/Rp.txt')
P0, P1 = ld(sys.argv[1]), ld(sys.argv[2])
s = np.zeros(N, bool); s[np.concatenate([P0, P1, Rp])] = True
mS = s[LP].any(1)
np.savetxt(sys.argv[3], np.nonzero(mS)[0], fmt='%d')
print('allow_S2 lines', mS.sum())
