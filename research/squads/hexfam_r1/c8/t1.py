import sys, time, random, numpy as np
sys.path.insert(0,'/home/user/degree-diameter/research/squads/hexfam_r1/c8')
from chart import *
t0=time.time()
ch = Chart(11); print('chart', time.time()-t0, len(ch.iso_vectors()), flush=True)
rng = random.Random(1); nrng=np.random.default_rng(1)
M = ch.random_orthogonal(rng, 5); o = matpow_order(M, 11); print('order', o, flush=True)
label,size,ov = cyc_orbits(ch, M, np.zeros(5,dtype=np.int64)); print('orbits', time.time()-t0, len(size), ov.sum(), flush=True)
vids,A = orbit_graph(ch,label,size,ov); print('graph', time.time()-t0, A.shape, A.mean(), flush=True)
w = size[vids]
print(greedy_clique(w, A, nrng, 20)[0], time.time()-t0)
