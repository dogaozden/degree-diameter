import sys, time, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/hexfam_r2/c3')
sys.path.insert(0, '/home/user/degree-diameter/research/projects/hexagon-family/tools')
from lib import *
from e7roots import e7_roots, subsystem
q = 11
t0 = time.time()
simple, R = e7_roots(q)
print('roots', len(R), 'simple', simple.shape, round(time.time()-t0,1), flush=True)
G = Geo(q)
print('N', G.N, flush=True)
t0 = time.time()
perm = G.perm(reflection_matrix(simple[0], q))
print('perm time', round(time.time()-t0,2), flush=True)
