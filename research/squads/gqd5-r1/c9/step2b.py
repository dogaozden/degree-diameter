import sys, time; sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r1/c9')
from lab import *
from ls_indep import local_indep
t=time.time()
best=[]
for s in range(20):
    S = local_indep(G.con, iters=20000, seed=s, target=21)
    if len(S) > len(best): best = S
    if len(best) >= 21: break
print('spread LS best', len(best), '%.1fs'%(time.time()-t))
np.save('/home/user/degree-diameter/research/squads/gqd5-r1/c9/spread_ls.npy', np.array(best))
O=[]
for s in range(20):
    S = local_indep(G.col, iters=20000, seed=s, target=26)
    if len(S) > len(O): O = S
    if len(O) >= 26: break
print('ovoid LS best', len(O))
np.save('/home/user/degree-diameter/research/squads/gqd5-r1/c9/ovoid_ls.npy', np.array(O))
