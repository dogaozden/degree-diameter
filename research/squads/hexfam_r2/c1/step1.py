import sys, time, pickle
sys.path.insert(0, '/home/user/degree-diameter/research/projects/hexagon-family/tools')
import numpy as np
from q6lib import Geo, orbits
from g2gens import root_elements
t = time.time()
G = Geo(9)
print('N', G.N, 'L', G.L, 'load', round(time.time()-t,2), flush=True)
R = root_elements(G)
print('roots', [(n, m is not None) for n, m in R], round(time.time()-t,2), flush=True)
mats = {n: m for n, m in R}
perms = {n: G.perm(m) for n, m in R}
pickle.dump({'mats': mats, 'perms': perms}, open('roots9.pkl', 'wb'))
print('done', round(time.time()-t,2))
