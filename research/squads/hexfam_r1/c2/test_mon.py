import sys; sys.path.insert(0,'/home/user/degree-diameter/research/squads/hexfam_r1/c2')
from common import *
t=time.time()
mons = monomial_phi_group()
print('monomial phi-stabilizer size', len(mons), time.time()-t, flush=True)
for M in mons[:3]: print(M)
